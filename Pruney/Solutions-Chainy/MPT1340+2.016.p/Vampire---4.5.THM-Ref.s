%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  279 ( 606 expanded)
%              Number of leaves         :   61 ( 291 expanded)
%              Depth                    :   24
%              Number of atoms          : 1234 (2595 expanded)
%              Number of equality atoms :  174 ( 422 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f740,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f101,f105,f109,f115,f119,f131,f133,f143,f164,f168,f173,f191,f204,f214,f222,f228,f250,f256,f283,f295,f297,f315,f354,f359,f397,f419,f432,f445,f453,f533,f555,f572,f593,f701,f706,f712,f717,f739])).

fof(f739,plain,
    ( ~ spl3_37
    | ~ spl3_36
    | ~ spl3_6
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f737,f715,f95,f286,f291])).

% (23496)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (23500)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (23490)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (23499)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (23488)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (23497)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f291,plain,
    ( spl3_37
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f286,plain,
    ( spl3_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f95,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f715,plain,
    ( spl3_78
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f737,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_78 ),
    inference(resolution,[],[f716,f96])).

fof(f96,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f716,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) )
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f715])).

fof(f717,plain,
    ( ~ spl3_6
    | ~ spl3_37
    | ~ spl3_36
    | spl3_78
    | spl3_77 ),
    inference(avatar_split_clause,[],[f713,f710,f715,f286,f291,f95])).

fof(f710,plain,
    ( spl3_77
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f713,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | spl3_77 ),
    inference(resolution,[],[f711,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f711,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_77 ),
    inference(avatar_component_clause,[],[f710])).

fof(f712,plain,
    ( ~ spl3_16
    | ~ spl3_6
    | ~ spl3_2
    | ~ spl3_77
    | spl3_76 ),
    inference(avatar_split_clause,[],[f708,f699,f710,f79,f95,f154])).

fof(f154,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f79,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f699,plain,
    ( spl3_76
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f708,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_76 ),
    inference(superposition,[],[f700,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f700,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | spl3_76 ),
    inference(avatar_component_clause,[],[f699])).

fof(f706,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | ~ spl3_18
    | ~ spl3_33
    | ~ spl3_41
    | spl3_75 ),
    inference(avatar_split_clause,[],[f705,f696,f357,f258,f171,f291,f286])).

fof(f171,plain,
    ( spl3_18
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f258,plain,
    ( spl3_33
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f357,plain,
    ( spl3_41
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f696,plain,
    ( spl3_75
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f705,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_33
    | ~ spl3_41
    | spl3_75 ),
    inference(trivial_inequality_removal,[],[f704])).

fof(f704,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_33
    | ~ spl3_41
    | spl3_75 ),
    inference(forward_demodulation,[],[f703,f259])).

fof(f259,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f703,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_18
    | ~ spl3_41
    | spl3_75 ),
    inference(trivial_inequality_removal,[],[f702])).

fof(f702,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_18
    | ~ spl3_41
    | spl3_75 ),
    inference(superposition,[],[f697,f379])).

fof(f379,plain,
    ( ! [X6,X7] :
        ( k1_relat_1(sK2) = k2_relset_1(X7,X6,k2_funct_1(sK2))
        | ~ v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_relset_1(X6,X7,sK2) != X7 )
    | ~ spl3_18
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f362,f172])).

fof(f172,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f362,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_relset_1(X6,X7,sK2) != X7
        | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(X7,X6,k2_funct_1(sK2)) )
    | ~ spl3_41 ),
    inference(resolution,[],[f358,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f358,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f357])).

fof(f697,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_75 ),
    inference(avatar_component_clause,[],[f696])).

fof(f701,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | ~ spl3_75
    | ~ spl3_76
    | ~ spl3_33
    | ~ spl3_40
    | ~ spl3_41
    | spl3_46
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f694,f570,f443,f357,f352,f258,f699,f696,f291,f286])).

fof(f352,plain,
    ( spl3_40
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(k2_funct_1(sK2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f443,plain,
    ( spl3_46
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f570,plain,
    ( spl3_63
  <=> ! [X3,X2] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f694,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_33
    | ~ spl3_40
    | ~ spl3_41
    | spl3_46
    | ~ spl3_63 ),
    inference(trivial_inequality_removal,[],[f693])).

fof(f693,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_33
    | ~ spl3_40
    | ~ spl3_41
    | spl3_46
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f692,f259])).

fof(f692,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_40
    | ~ spl3_41
    | spl3_46
    | ~ spl3_63 ),
    inference(superposition,[],[f444,f691])).

fof(f691,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0 )
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0 )
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(resolution,[],[f631,f353])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f352])).

fof(f631,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
        | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0 )
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(resolution,[],[f571,f358])).

fof(f571,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 )
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f570])).

fof(f444,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f443])).

fof(f593,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_42
    | spl3_61 ),
    inference(avatar_split_clause,[],[f591,f563,f382,f79,f95])).

fof(f382,plain,
    ( spl3_42
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(sK2,X2,X3)
        | k2_relset_1(X2,X3,sK2) != X3
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f563,plain,
    ( spl3_61
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | spl3_61 ),
    inference(resolution,[],[f564,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f564,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f563])).

fof(f572,plain,
    ( ~ spl3_61
    | spl3_63
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f557,f531,f570,f563])).

fof(f531,plain,
    ( spl3_56
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f557,plain,
    ( ! [X2,X3] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_56 ),
    inference(resolution,[],[f532,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f532,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f531])).

fof(f555,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f533,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | spl3_56
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f528,f451,f430,f258,f245,f193,f117,f113,f107,f99,f531,f291,f286])).

fof(f99,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f107,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f113,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f117,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f193,plain,
    ( spl3_23
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f245,plain,
    ( spl3_30
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f430,plain,
    ( spl3_45
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f451,plain,
    ( spl3_47
  <=> ! [X1,X0] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f528,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(trivial_inequality_removal,[],[f527])).

fof(f527,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_33
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f526,f259])).

fof(f526,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f525,f194])).

fof(f194,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f525,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f524,f114])).

fof(f114,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f524,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f523,f431])).

fof(f431,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f430])).

fof(f523,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f522,f194])).

fof(f522,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f521,f114])).

fof(f521,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f520,f194])).

fof(f520,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f519,f114])).

fof(f519,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f518,f194])).

fof(f518,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f516,f114])).

fof(f516,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(resolution,[],[f471,f100])).

fof(f100,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f471,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f470,f246])).

fof(f246,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f245])).

fof(f470,plain,
    ( ! [X1] :
        ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f469,f118])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f469,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f468,f246])).

fof(f468,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f467,f118])).

fof(f467,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f466,f246])).

fof(f466,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f465,f118])).

fof(f465,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f464,f246])).

fof(f464,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f455,f118])).

fof(f455,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_47 ),
    inference(resolution,[],[f452,f108])).

fof(f108,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f451])).

fof(f453,plain,
    ( ~ spl3_6
    | spl3_47
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f449,f79,f451,f95])).

fof(f449,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f80])).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f445,plain,
    ( ~ spl3_46
    | spl3_35
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f441,f430,f281,f443])).

fof(f281,plain,
    ( spl3_35
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f441,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_35
    | ~ spl3_45 ),
    inference(superposition,[],[f282,f431])).

fof(f282,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_35 ),
    inference(avatar_component_clause,[],[f281])).

fof(f432,plain,
    ( ~ spl3_37
    | spl3_45
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f428,f417,f245,f193,f136,f121,f430,f291])).

fof(f121,plain,
    ( spl3_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f136,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f417,plain,
    ( spl3_44
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f428,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(trivial_inequality_removal,[],[f427])).

fof(f427,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f426,f122])).

fof(f122,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f426,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f425,f246])).

fof(f425,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f424,f194])).

fof(f424,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f423,f246])).

fof(f423,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f420,f194])).

fof(f420,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14
    | ~ spl3_44 ),
    inference(resolution,[],[f418,f137])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f418,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f417])).

fof(f419,plain,
    ( ~ spl3_6
    | spl3_44
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f415,f79,f417,f95])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f71,f80])).

fof(f397,plain,
    ( ~ spl3_37
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f396,f382,f245,f193,f136,f121,f291])).

fof(f396,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_30
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f395,f246])).

fof(f395,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_23
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f394,f194])).

fof(f394,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f390,f122])).

fof(f390,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(resolution,[],[f383,f137])).

fof(f383,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,sK2) != X3
        | ~ v1_funct_2(sK2,X2,X3) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f382])).

fof(f359,plain,
    ( ~ spl3_6
    | spl3_41
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f355,f79,f357,f95])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f80])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f354,plain,
    ( ~ spl3_6
    | spl3_40
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f350,f79,f352,f95])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f80])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f315,plain,
    ( ~ spl3_28
    | spl3_29
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f309,f254,f212,f226,f220])).

fof(f220,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f226,plain,
    ( spl3_29
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f212,plain,
    ( spl3_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f254,plain,
    ( spl3_32
  <=> ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f309,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(resolution,[],[f255,f213])).

fof(f213,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f254])).

fof(f297,plain,
    ( spl3_37
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f276,f245,f220,f291])).

fof(f276,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(superposition,[],[f221,f246])).

fof(f221,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f295,plain,
    ( spl3_36
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f274,f245,f212,f286])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(superposition,[],[f213,f246])).

fof(f283,plain,
    ( ~ spl3_35
    | spl3_13
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f279,f245,f193,f129,f281])).

fof(f129,plain,
    ( spl3_13
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f279,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_13
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f270,f194])).

fof(f270,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13
    | ~ spl3_30 ),
    inference(superposition,[],[f130,f246])).

fof(f130,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f256,plain,
    ( ~ spl3_6
    | spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f252,f248,f254,f95])).

fof(f248,plain,
    ( spl3_31
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0) )
    | spl3_31 ),
    inference(resolution,[],[f249,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f249,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl3_30
    | ~ spl3_31
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f242,f136,f248,f245])).

fof(f242,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f240,f137])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl3_14 ),
    inference(resolution,[],[f239,f137])).

fof(f239,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f186,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f63,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f228,plain,
    ( spl3_8
    | ~ spl3_7
    | ~ spl3_29
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f210,f193,f226,f99,f103])).

fof(f103,plain,
    ( spl3_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f210,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_23 ),
    inference(superposition,[],[f57,f194])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f222,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f209,f193,f141,f220])).

fof(f141,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f209,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(superposition,[],[f142,f194])).

fof(f142,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f214,plain,
    ( spl3_26
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f206,f193,f136,f212])).

fof(f206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(superposition,[],[f137,f194])).

fof(f204,plain,
    ( spl3_23
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f202,f189,f121,f193])).

fof(f189,plain,
    ( spl3_22
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f202,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(superposition,[],[f122,f190])).

fof(f190,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl3_22
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f187,f136,f189])).

fof(f187,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f66,f137])).

fof(f173,plain,
    ( ~ spl3_16
    | ~ spl3_6
    | spl3_18
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f169,f79,f171,f95,f154])).

fof(f169,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f60,f80])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f168,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f167,f117,f113,f87,f136])).

fof(f87,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f167,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f166,f118])).

fof(f166,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f88,f114])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f164,plain,
    ( ~ spl3_4
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_4
    | spl3_16 ),
    inference(subsumption_resolution,[],[f88,f161])).

fof(f161,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_16 ),
    inference(resolution,[],[f155,f65])).

fof(f155,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f143,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f139,f117,f113,f91,f141])).

fof(f91,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f139,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f126,f118])).

fof(f126,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f92,f114])).

fof(f92,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f133,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f132,f117,f113,f83,f121])).

fof(f83,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (23508)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f132,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f124,f118])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f84,f114])).

fof(f84,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f131,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f127,f117,f113,f75,f129])).

fof(f75,plain,
    ( spl3_1
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f127,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f123,f118])).

fof(f123,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f76,f114])).

fof(f76,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f119,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f111,f107,f117])).

% (23489)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f111,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f55,f108])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f115,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f110,f99,f113])).

fof(f110,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f100])).

fof(f109,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f46,f107])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f105,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f47,f103])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f97,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f95])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f83])).

fof(f52,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f53,f79])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f75])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (23509)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (23503)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (23501)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (23495)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (23494)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (23509)Refutation not found, incomplete strategy% (23509)------------------------------
% 0.22/0.47  % (23509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23509)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23509)Memory used [KB]: 10618
% 0.22/0.47  % (23509)Time elapsed: 0.050 s
% 0.22/0.47  % (23509)------------------------------
% 0.22/0.47  % (23509)------------------------------
% 0.22/0.48  % (23501)Refutation not found, incomplete strategy% (23501)------------------------------
% 0.22/0.48  % (23501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23501)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23501)Memory used [KB]: 6140
% 0.22/0.48  % (23501)Time elapsed: 0.060 s
% 0.22/0.48  % (23501)------------------------------
% 0.22/0.48  % (23501)------------------------------
% 0.22/0.48  % (23502)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (23495)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f740,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f97,f101,f105,f109,f115,f119,f131,f133,f143,f164,f168,f173,f191,f204,f214,f222,f228,f250,f256,f283,f295,f297,f315,f354,f359,f397,f419,f432,f445,f453,f533,f555,f572,f593,f701,f706,f712,f717,f739])).
% 0.22/0.49  fof(f739,plain,(
% 0.22/0.49    ~spl3_37 | ~spl3_36 | ~spl3_6 | ~spl3_78),
% 0.22/0.49    inference(avatar_split_clause,[],[f737,f715,f95,f286,f291])).
% 0.22/0.49  % (23496)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (23500)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (23490)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (23499)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (23488)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (23497)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    spl3_37 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    spl3_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f715,plain,(
% 0.22/0.50    spl3_78 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.22/0.50  fof(f737,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_6 | ~spl3_78)),
% 0.22/0.50    inference(resolution,[],[f716,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f716,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))) ) | ~spl3_78),
% 0.22/0.50    inference(avatar_component_clause,[],[f715])).
% 0.22/0.50  fof(f717,plain,(
% 0.22/0.50    ~spl3_6 | ~spl3_37 | ~spl3_36 | spl3_78 | spl3_77),
% 0.22/0.50    inference(avatar_split_clause,[],[f713,f710,f715,f286,f291,f95])).
% 0.22/0.50  fof(f710,plain,(
% 0.22/0.50    spl3_77 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.22/0.50  fof(f713,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | spl3_77),
% 0.22/0.50    inference(resolution,[],[f711,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.22/0.50  fof(f711,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_77),
% 0.22/0.50    inference(avatar_component_clause,[],[f710])).
% 0.22/0.50  fof(f712,plain,(
% 0.22/0.50    ~spl3_16 | ~spl3_6 | ~spl3_2 | ~spl3_77 | spl3_76),
% 0.22/0.50    inference(avatar_split_clause,[],[f708,f699,f710,f79,f95,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl3_16 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f699,plain,(
% 0.22/0.50    spl3_76 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.22/0.50  fof(f708,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_76),
% 0.22/0.50    inference(superposition,[],[f700,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.50  fof(f700,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | spl3_76),
% 0.22/0.50    inference(avatar_component_clause,[],[f699])).
% 0.22/0.50  fof(f706,plain,(
% 0.22/0.50    ~spl3_36 | ~spl3_37 | ~spl3_18 | ~spl3_33 | ~spl3_41 | spl3_75),
% 0.22/0.50    inference(avatar_split_clause,[],[f705,f696,f357,f258,f171,f291,f286])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl3_18 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    spl3_33 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    spl3_41 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.50  fof(f696,plain,(
% 0.22/0.50    spl3_75 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.22/0.50  fof(f705,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_18 | ~spl3_33 | ~spl3_41 | spl3_75)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f704])).
% 0.22/0.50  fof(f704,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_18 | ~spl3_33 | ~spl3_41 | spl3_75)),
% 0.22/0.50    inference(forward_demodulation,[],[f703,f259])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f258])).
% 0.22/0.50  fof(f703,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_18 | ~spl3_41 | spl3_75)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f702])).
% 0.22/0.50  fof(f702,plain,(
% 0.22/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_18 | ~spl3_41 | spl3_75)),
% 0.22/0.50    inference(superposition,[],[f697,f379])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k1_relat_1(sK2) = k2_relset_1(X7,X6,k2_funct_1(sK2)) | ~v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_relset_1(X6,X7,sK2) != X7) ) | (~spl3_18 | ~spl3_41)),
% 0.22/0.50    inference(forward_demodulation,[],[f362,f172])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f171])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    ( ! [X6,X7] : (~v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_relset_1(X6,X7,sK2) != X7 | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(X7,X6,k2_funct_1(sK2))) ) | ~spl3_41),
% 0.22/0.50    inference(resolution,[],[f358,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_41),
% 0.22/0.50    inference(avatar_component_clause,[],[f357])).
% 0.22/0.50  fof(f697,plain,(
% 0.22/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_75),
% 0.22/0.50    inference(avatar_component_clause,[],[f696])).
% 0.22/0.50  fof(f701,plain,(
% 0.22/0.50    ~spl3_36 | ~spl3_37 | ~spl3_75 | ~spl3_76 | ~spl3_33 | ~spl3_40 | ~spl3_41 | spl3_46 | ~spl3_63),
% 0.22/0.50    inference(avatar_split_clause,[],[f694,f570,f443,f357,f352,f258,f699,f696,f291,f286])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    spl3_40 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_funct_1(sK2),X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.50  fof(f443,plain,(
% 0.22/0.50    spl3_46 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.50  fof(f570,plain,(
% 0.22/0.50    spl3_63 <=> ! [X3,X2] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.22/0.50  fof(f694,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_33 | ~spl3_40 | ~spl3_41 | spl3_46 | ~spl3_63)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f693])).
% 0.22/0.50  fof(f693,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_33 | ~spl3_40 | ~spl3_41 | spl3_46 | ~spl3_63)),
% 0.22/0.50    inference(forward_demodulation,[],[f692,f259])).
% 0.22/0.50  fof(f692,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_40 | ~spl3_41 | spl3_46 | ~spl3_63)),
% 0.22/0.50    inference(superposition,[],[f444,f691])).
% 0.22/0.50  fof(f691,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0) ) | (~spl3_40 | ~spl3_41 | ~spl3_63)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f690])).
% 0.22/0.50  fof(f690,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0) ) | (~spl3_40 | ~spl3_41 | ~spl3_63)),
% 0.22/0.50    inference(resolution,[],[f631,f353])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(sK2),X1,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f352])).
% 0.22/0.50  fof(f631,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_2(k2_funct_1(sK2),X0,X1) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0) ) | (~spl3_41 | ~spl3_63)),
% 0.22/0.50    inference(resolution,[],[f571,f358])).
% 0.22/0.50  fof(f571,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3) ) | ~spl3_63),
% 0.22/0.50    inference(avatar_component_clause,[],[f570])).
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f443])).
% 0.22/0.50  fof(f593,plain,(
% 0.22/0.50    ~spl3_6 | ~spl3_2 | spl3_42 | spl3_61),
% 0.22/0.50    inference(avatar_split_clause,[],[f591,f563,f382,f79,f95])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    spl3_42 <=> ! [X3,X2] : (~v1_funct_2(sK2,X2,X3) | k2_relset_1(X2,X3,sK2) != X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.22/0.50  fof(f563,plain,(
% 0.22/0.50    spl3_61 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.22/0.50  fof(f591,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | spl3_61),
% 0.22/0.50    inference(resolution,[],[f564,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  fof(f564,plain,(
% 0.22/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl3_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f563])).
% 0.22/0.50  fof(f572,plain,(
% 0.22/0.50    ~spl3_61 | spl3_63 | ~spl3_56),
% 0.22/0.50    inference(avatar_split_clause,[],[f557,f531,f570,f563])).
% 0.22/0.50  fof(f531,plain,(
% 0.22/0.50    spl3_56 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.50  fof(f557,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_56),
% 0.22/0.50    inference(resolution,[],[f532,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f532,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK2)) | ~spl3_56),
% 0.22/0.50    inference(avatar_component_clause,[],[f531])).
% 0.22/0.50  fof(f555,plain,(
% 0.22/0.50    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f533,plain,(
% 0.22/0.50    ~spl3_36 | ~spl3_37 | spl3_56 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_33 | ~spl3_45 | ~spl3_47),
% 0.22/0.50    inference(avatar_split_clause,[],[f528,f451,f430,f258,f245,f193,f117,f113,f107,f99,f531,f291,f286])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl3_23 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    spl3_30 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    spl3_45 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    spl3_47 <=> ! [X1,X0] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X0) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.50  fof(f528,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_33 | ~spl3_45 | ~spl3_47)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f527])).
% 0.22/0.50  fof(f527,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_33 | ~spl3_45 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f526,f259])).
% 0.22/0.50  fof(f526,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_45 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f525,f194])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f525,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_45 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f524,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f524,plain,(
% 0.22/0.50    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_45 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f523,f431])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f430])).
% 0.22/0.50  fof(f523,plain,(
% 0.22/0.50    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f522,f194])).
% 0.22/0.50  fof(f522,plain,(
% 0.22/0.50    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f521,f114])).
% 0.22/0.50  fof(f521,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f520,f194])).
% 0.22/0.50  fof(f520,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f519,f114])).
% 0.22/0.50  fof(f519,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_23 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f518,f194])).
% 0.22/0.50  fof(f518,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f516,f114])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(resolution,[],[f471,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f471,plain,(
% 0.22/0.50    ( ! [X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f470,f246])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f245])).
% 0.22/0.50  fof(f470,plain,(
% 0.22/0.50    ( ! [X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f469,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f469,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f468,f246])).
% 0.22/0.50  fof(f468,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f467,f118])).
% 0.22/0.50  fof(f467,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f466,f246])).
% 0.22/0.50  fof(f466,plain,(
% 0.22/0.50    ( ! [X1] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f465,f118])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_30 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f464,f246])).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_47)),
% 0.22/0.50    inference(forward_demodulation,[],[f455,f118])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_47)),
% 0.22/0.50    inference(resolution,[],[f452,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)) ) | ~spl3_47),
% 0.22/0.50    inference(avatar_component_clause,[],[f451])).
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    ~spl3_6 | spl3_47 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f449,f79,f451,f95])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) ) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f56,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f79])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.50  fof(f445,plain,(
% 0.22/0.50    ~spl3_46 | spl3_35 | ~spl3_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f441,f430,f281,f443])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    spl3_35 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_35 | ~spl3_45)),
% 0.22/0.50    inference(superposition,[],[f282,f431])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f281])).
% 0.22/0.50  fof(f432,plain,(
% 0.22/0.50    ~spl3_37 | spl3_45 | ~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44),
% 0.22/0.50    inference(avatar_split_clause,[],[f428,f417,f245,f193,f136,f121,f430,f291])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl3_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    spl3_44 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f427])).
% 0.22/0.50  fof(f427,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f426,f122])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f425,f246])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f424,f194])).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f423,f246])).
% 0.22/0.50  fof(f423,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_14 | ~spl3_23 | ~spl3_44)),
% 0.22/0.50    inference(forward_demodulation,[],[f420,f194])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_14 | ~spl3_44)),
% 0.22/0.50    inference(resolution,[],[f418,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_44),
% 0.22/0.50    inference(avatar_component_clause,[],[f417])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    ~spl3_6 | spl3_44 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f415,f79,f417,f95])).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f71,f80])).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ~spl3_37 | ~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_42),
% 0.22/0.50    inference(avatar_split_clause,[],[f396,f382,f245,f193,f136,f121,f291])).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_30 | ~spl3_42)),
% 0.22/0.50    inference(forward_demodulation,[],[f395,f246])).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_14 | ~spl3_23 | ~spl3_42)),
% 0.22/0.50    inference(forward_demodulation,[],[f394,f194])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_12 | ~spl3_14 | ~spl3_42)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f393])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_12 | ~spl3_14 | ~spl3_42)),
% 0.22/0.50    inference(forward_demodulation,[],[f390,f122])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_14 | ~spl3_42)),
% 0.22/0.50    inference(resolution,[],[f383,f137])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,sK2) != X3 | ~v1_funct_2(sK2,X2,X3)) ) | ~spl3_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f382])).
% 0.22/0.50  fof(f359,plain,(
% 0.22/0.50    ~spl3_6 | spl3_41 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f355,f79,f357,f95])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f70,f80])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    ~spl3_6 | spl3_40 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f350,f79,f352,f95])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_2(k2_funct_1(sK2),X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f69,f80])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    ~spl3_28 | spl3_29 | ~spl3_26 | ~spl3_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f309,f254,f212,f226,f220])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl3_28 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    spl3_29 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl3_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    spl3_32 <=> ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_26 | ~spl3_32)),
% 0.22/0.50    inference(resolution,[],[f255,f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f212])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0) | ~v1_funct_2(sK2,k2_struct_0(sK0),X0)) ) | ~spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f254])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    spl3_37 | ~spl3_28 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f276,f245,f220,f291])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_28 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f221,f246])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f220])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    spl3_36 | ~spl3_26 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f274,f245,f212,f286])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_26 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f213,f246])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    ~spl3_35 | spl3_13 | ~spl3_23 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f279,f245,f193,f129,f281])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl3_13 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_13 | ~spl3_23 | ~spl3_30)),
% 0.22/0.50    inference(forward_demodulation,[],[f270,f194])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2) | (spl3_13 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f130,f246])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f129])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ~spl3_6 | spl3_32 | spl3_31),
% 0.22/0.50    inference(avatar_split_clause,[],[f252,f248,f254,f95])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    spl3_31 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0)) ) | spl3_31),
% 0.22/0.50    inference(resolution,[],[f249,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f248])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl3_30 | ~spl3_31 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f242,f136,f248,f245])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_14),
% 0.22/0.50    inference(resolution,[],[f240,f137])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0) ) | ~spl3_14),
% 0.22/0.50    inference(resolution,[],[f239,f137])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.50    inference(resolution,[],[f186,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.50    inference(resolution,[],[f63,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl3_8 | ~spl3_7 | ~spl3_29 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f210,f193,f226,f99,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl3_8 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_23),
% 0.22/0.50    inference(superposition,[],[f57,f194])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl3_28 | ~spl3_15 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f209,f193,f141,f220])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_15 | ~spl3_23)),
% 0.22/0.50    inference(superposition,[],[f142,f194])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl3_26 | ~spl3_14 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f206,f193,f136,f212])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_23)),
% 0.22/0.50    inference(superposition,[],[f137,f194])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    spl3_23 | ~spl3_12 | ~spl3_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f202,f189,f121,f193])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    spl3_22 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_12 | ~spl3_22)),
% 0.22/0.50    inference(superposition,[],[f122,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f189])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl3_22 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f187,f136,f189])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_14),
% 0.22/0.50    inference(resolution,[],[f66,f137])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ~spl3_16 | ~spl3_6 | spl3_18 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f169,f79,f171,f95,f154])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.22/0.50    inference(resolution,[],[f60,f80])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl3_14 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f167,f117,f113,f87,f136])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f166,f118])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f88,f114])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~spl3_4 | spl3_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    $false | (~spl3_4 | spl3_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_16),
% 0.22/0.50    inference(resolution,[],[f155,f65])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f154])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl3_15 | ~spl3_5 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f139,f117,f113,f91,f141])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f126,f118])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.22/0.50    inference(superposition,[],[f92,f114])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_12 | ~spl3_3 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f132,f117,f113,f83,f121])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  % (23508)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f124,f118])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.22/0.50    inference(superposition,[],[f84,f114])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ~spl3_13 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f127,f117,f113,f75,f129])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl3_1 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.22/0.51    inference(forward_demodulation,[],[f123,f118])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10)),
% 0.22/0.51    inference(superposition,[],[f76,f114])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f75])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_11 | ~spl3_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f111,f107,f117])).
% 0.22/0.51  % (23489)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f55,f108])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl3_10 | ~spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f110,f99,f113])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.51    inference(resolution,[],[f55,f100])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    spl3_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f107])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    l1_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f43,f42,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f103])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl3_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f99])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl3_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f95])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f50,f91])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f87])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f83])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f79])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f75])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (23495)------------------------------
% 0.22/0.51  % (23495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23495)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (23495)Memory used [KB]: 11257
% 0.22/0.51  % (23495)Time elapsed: 0.021 s
% 0.22/0.51  % (23495)------------------------------
% 0.22/0.51  % (23495)------------------------------
% 0.22/0.51  % (23493)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (23505)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (23484)Success in time 0.148 s
%------------------------------------------------------------------------------
