%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:21 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 477 expanded)
%              Number of leaves         :   62 ( 231 expanded)
%              Depth                    :    9
%              Number of atoms          :  807 (1565 expanded)
%              Number of equality atoms :  136 ( 280 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (31352)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (31350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (31347)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (31372)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (31358)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (31354)Termination reason: Refutation not found, incomplete strategy

% (31354)Memory used [KB]: 1791
% (31354)Time elapsed: 0.125 s
% (31354)------------------------------
% (31354)------------------------------
% (31367)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (31361)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (31347)Refutation not found, incomplete strategy% (31347)------------------------------
% (31347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31347)Termination reason: Refutation not found, incomplete strategy

% (31347)Memory used [KB]: 10746
% (31347)Time elapsed: 0.138 s
% (31347)------------------------------
% (31347)------------------------------
% (31360)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (31364)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (31366)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f134,f139,f148,f153,f158,f163,f169,f175,f181,f187,f193,f204,f209,f226,f232,f238,f244,f261,f266,f271,f281,f286,f300,f311,f316,f321,f331,f349,f362,f363,f385,f406,f412,f467,f488,f496,f502,f506])).

fof(f506,plain,
    ( ~ spl3_9
    | ~ spl3_39
    | ~ spl3_38
    | spl3_59 ),
    inference(avatar_split_clause,[],[f504,f499,f308,f313,f119])).

fof(f119,plain,
    ( spl3_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f313,plain,
    ( spl3_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f308,plain,
    ( spl3_38
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

% (31356)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f499,plain,
    ( spl3_59
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f504,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | spl3_59 ),
    inference(resolution,[],[f501,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f501,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_59 ),
    inference(avatar_component_clause,[],[f499])).

fof(f502,plain,
    ( ~ spl3_59
    | spl3_49
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f497,f485,f409,f499])).

fof(f409,plain,
    ( spl3_49
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f485,plain,
    ( spl3_58
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f497,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_49
    | ~ spl3_58 ),
    inference(backward_demodulation,[],[f411,f487])).

fof(f487,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f485])).

fof(f411,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_49 ),
    inference(avatar_component_clause,[],[f409])).

fof(f496,plain,
    ( ~ spl3_9
    | ~ spl3_5
    | ~ spl3_39
    | ~ spl3_38
    | ~ spl3_42
    | spl3_57 ),
    inference(avatar_split_clause,[],[f495,f481,f328,f308,f313,f99,f119])).

fof(f99,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f328,plain,
    ( spl3_42
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f481,plain,
    ( spl3_57
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f495,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_42
    | spl3_57 ),
    inference(trivial_inequality_removal,[],[f494])).

fof(f494,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_42
    | spl3_57 ),
    inference(forward_demodulation,[],[f492,f330])).

fof(f330,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f328])).

fof(f492,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | spl3_57 ),
    inference(resolution,[],[f483,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f483,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f481])).

fof(f488,plain,
    ( ~ spl3_46
    | ~ spl3_44
    | ~ spl3_57
    | ~ spl3_45
    | spl3_58
    | ~ spl3_22
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f479,f464,f197,f485,f359,f481,f346,f375])).

fof(f375,plain,
    ( spl3_46
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f346,plain,
    ( spl3_44
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f359,plain,
    ( spl3_45
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f197,plain,
    ( spl3_22
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f464,plain,
    ( spl3_56
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f479,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f475,f199])).

fof(f199,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f475,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_56 ),
    inference(trivial_inequality_removal,[],[f470])).

fof(f470,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_56 ),
    inference(superposition,[],[f68,f466])).

fof(f466,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f464])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f467,plain,
    ( ~ spl3_9
    | ~ spl3_38
    | ~ spl3_5
    | ~ spl3_39
    | spl3_56
    | ~ spl3_25
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f462,f328,f223,f464,f313,f99,f308,f119])).

fof(f223,plain,
    ( spl3_25
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f462,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_25
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f461,f225])).

fof(f225,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f461,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f460])).

fof(f460,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(superposition,[],[f368,f330])).

fof(f368,plain,(
    ! [X6,X8,X7] :
      ( k2_relset_1(X7,X8,X6) != X8
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ v2_funct_1(X6)
      | ~ v1_funct_2(X6,X7,X8)
      | ~ v1_funct_1(X6)
      | k2_relset_1(X8,X7,k2_funct_1(X6)) = k2_relat_1(k2_funct_1(X6)) ) ),
    inference(resolution,[],[f67,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f412,plain,
    ( ~ spl3_49
    | spl3_40
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f407,f403,f318,f409])).

fof(f318,plain,
    ( spl3_40
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f403,plain,
    ( spl3_48
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f407,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_40
    | ~ spl3_48 ),
    inference(backward_demodulation,[],[f320,f405])).

fof(f405,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f403])).

fof(f320,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f406,plain,
    ( spl3_48
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_39
    | ~ spl3_38
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f401,f328,f308,f313,f119,f99,f403])).

fof(f401,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f400])).

fof(f400,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_42 ),
    inference(superposition,[],[f68,f330])).

fof(f385,plain,
    ( ~ spl3_23
    | ~ spl3_5
    | ~ spl3_9
    | spl3_46 ),
    inference(avatar_split_clause,[],[f383,f375,f119,f99,f201])).

fof(f201,plain,
    ( spl3_23
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f383,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_46 ),
    inference(resolution,[],[f377,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f377,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f375])).

fof(f363,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f362,plain,
    ( spl3_45
    | ~ spl3_9
    | ~ spl3_5
    | ~ spl3_39
    | ~ spl3_38
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f357,f328,f308,f313,f99,f119,f359])).

fof(f357,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f356])).

fof(f356,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_42 ),
    inference(superposition,[],[f66,f330])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f349,plain,
    ( spl3_44
    | ~ spl3_9
    | ~ spl3_5
    | ~ spl3_39
    | ~ spl3_38
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f344,f328,f308,f313,f99,f119,f346])).

fof(f344,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(superposition,[],[f65,f330])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f331,plain,
    ( spl3_42
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f305,f297,f283,f328])).

fof(f283,plain,
    ( spl3_35
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f297,plain,
    ( spl3_37
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f305,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f285,f299])).

fof(f299,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f297])).

fof(f285,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f283])).

fof(f321,plain,
    ( ~ spl3_40
    | spl3_32
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f303,f297,f268,f318])).

fof(f268,plain,
    ( spl3_32
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f303,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_32
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f270,f299])).

fof(f270,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f316,plain,
    ( spl3_39
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f302,f297,f263,f313])).

fof(f263,plain,
    ( spl3_31
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f265,f299])).

fof(f265,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f263])).

fof(f311,plain,
    ( spl3_38
    | ~ spl3_30
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f301,f297,f258,f308])).

fof(f258,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f301,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_30
    | ~ spl3_37 ),
    inference(backward_demodulation,[],[f260,f299])).

fof(f260,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f300,plain,
    ( ~ spl3_30
    | spl3_36
    | spl3_37
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f291,f278,f263,f297,f293,f258])).

fof(f293,plain,
    ( spl3_36
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f278,plain,
    ( spl3_34
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f291,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f290,f280])).

fof(f280,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f278])).

fof(f290,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_31 ),
    inference(resolution,[],[f64,f265])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f286,plain,
    ( spl3_35
    | ~ spl3_27
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f251,f241,f235,f283])).

fof(f235,plain,
    ( spl3_27
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f241,plain,
    ( spl3_28
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f251,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f237,f243])).

fof(f243,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f241])).

fof(f237,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f235])).

fof(f281,plain,
    ( spl3_34
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f250,f241,f229,f278])).

fof(f229,plain,
    ( spl3_26
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f250,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f231,f243])).

fof(f231,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f271,plain,
    ( ~ spl3_32
    | spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f248,f241,f184,f268])).

fof(f184,plain,
    ( spl3_20
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f248,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_20
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f186,f243])).

fof(f186,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f266,plain,
    ( spl3_31
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f247,f241,f172,f263])).

fof(f172,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f247,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f174,f243])).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f261,plain,
    ( spl3_30
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f246,f241,f166,f258])).

fof(f166,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f246,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f168,f243])).

fof(f168,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f244,plain,
    ( spl3_28
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f239,f235,f178,f241])).

fof(f178,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f239,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f180,f237])).

fof(f180,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f238,plain,
    ( spl3_27
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f233,f172,f235])).

fof(f233,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f58,f174])).

fof(f232,plain,
    ( spl3_26
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f227,f172,f229])).

fof(f227,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f57,f174])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f226,plain,
    ( spl3_25
    | ~ spl3_23
    | ~ spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f220,f99,f119,f201,f223])).

fof(f220,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f55,f101])).

fof(f101,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f209,plain,
    ( ~ spl3_18
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_18
    | spl3_23 ),
    inference(subsumption_resolution,[],[f174,f206])).

fof(f206,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_23 ),
    inference(resolution,[],[f203,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f203,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( spl3_22
    | ~ spl3_23
    | ~ spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f194,f99,f119,f201,f197])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f53,f101])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f193,plain,
    ( ~ spl3_21
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f188,f89,f84,f190])).

fof(f190,plain,
    ( spl3_21
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f84,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f188,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3 ),
    inference(resolution,[],[f49,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f49,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f187,plain,
    ( ~ spl3_20
    | ~ spl3_11
    | spl3_13 ),
    inference(avatar_split_clause,[],[f182,f145,f131,f184])).

fof(f131,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f145,plain,
    ( spl3_13
  <=> r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f182,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_11
    | spl3_13 ),
    inference(forward_demodulation,[],[f147,f133])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f147,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f181,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f176,f150,f131,f178])).

fof(f150,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f176,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f152,f133])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f175,plain,
    ( spl3_18
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f170,f155,f131,f172])).

fof(f155,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f157,f133])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f169,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f160,f131,f166])).

fof(f160,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f162,f133])).

fof(f162,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f143,f136,f114,f160])).

fof(f114,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f136,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f143,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f116,f138])).

fof(f138,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f116,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f158,plain,
    ( spl3_15
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f142,f136,f109,f155])).

fof(f109,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f111,f138])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f141,f136,f104,f150])).

fof(f104,plain,
    ( spl3_6
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f141,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f106,f138])).

fof(f106,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f148,plain,
    ( ~ spl3_13
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f140,f136,f94,f145])).

fof(f94,plain,
    ( spl3_4
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f96,f138])).

fof(f96,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f139,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f129,f84,f136])).

fof(f129,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f48,f86])).

fof(f86,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f134,plain,
    ( spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f128,f79,f131])).

fof(f79,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f128,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f48,f81])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

% (31348)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f127,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f47,f124])).

fof(f124,plain,
    ( spl3_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f122,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f119])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f117,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f39,f114])).

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f40,f109])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f107,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.53  % (31354)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (31355)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (31362)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.44/0.54  % (31371)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.54  % (31365)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.54  % (31369)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.44/0.54  % (31359)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.44/0.54  % (31370)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.44/0.54  % (31354)Refutation not found, incomplete strategy% (31354)------------------------------
% 1.44/0.54  % (31354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (31363)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.44/0.54  % (31351)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.44/0.54  % (31357)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.44/0.54  % (31353)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.44/0.55  % (31349)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.44/0.55  % (31353)Refutation not found, incomplete strategy% (31353)------------------------------
% 1.44/0.55  % (31353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (31353)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (31353)Memory used [KB]: 10618
% 1.44/0.55  % (31353)Time elapsed: 0.121 s
% 1.44/0.55  % (31353)------------------------------
% 1.44/0.55  % (31353)------------------------------
% 1.44/0.55  % (31362)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  % (31352)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.44/0.55  % (31350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.44/0.55  % (31347)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.57/0.55  % (31372)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.57/0.56  % (31358)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.57/0.56  % (31354)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (31354)Memory used [KB]: 1791
% 1.57/0.56  % (31354)Time elapsed: 0.125 s
% 1.57/0.56  % (31354)------------------------------
% 1.57/0.56  % (31354)------------------------------
% 1.57/0.56  % (31367)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.57/0.56  % (31361)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.57/0.56  % (31347)Refutation not found, incomplete strategy% (31347)------------------------------
% 1.57/0.56  % (31347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (31347)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (31347)Memory used [KB]: 10746
% 1.57/0.56  % (31347)Time elapsed: 0.138 s
% 1.57/0.56  % (31347)------------------------------
% 1.57/0.56  % (31347)------------------------------
% 1.57/0.56  % (31360)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.57/0.56  % (31364)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.57/0.56  % (31366)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.57/0.56  fof(f507,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f134,f139,f148,f153,f158,f163,f169,f175,f181,f187,f193,f204,f209,f226,f232,f238,f244,f261,f266,f271,f281,f286,f300,f311,f316,f321,f331,f349,f362,f363,f385,f406,f412,f467,f488,f496,f502,f506])).
% 1.57/0.57  fof(f506,plain,(
% 1.57/0.57    ~spl3_9 | ~spl3_39 | ~spl3_38 | spl3_59),
% 1.57/0.57    inference(avatar_split_clause,[],[f504,f499,f308,f313,f119])).
% 1.57/0.57  fof(f119,plain,(
% 1.57/0.57    spl3_9 <=> v1_funct_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.57  fof(f313,plain,(
% 1.57/0.57    spl3_39 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.57/0.57  fof(f308,plain,(
% 1.57/0.57    spl3_38 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.57/0.57  % (31356)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.57/0.57  fof(f499,plain,(
% 1.57/0.57    spl3_59 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.57/0.57  fof(f504,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | spl3_59),
% 1.57/0.57    inference(resolution,[],[f501,f77])).
% 1.57/0.57  fof(f77,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f76])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.57/0.57    inference(equality_resolution,[],[f69])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.57    inference(flattening,[],[f36])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.57/0.57  fof(f501,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_59),
% 1.57/0.57    inference(avatar_component_clause,[],[f499])).
% 1.57/0.57  fof(f502,plain,(
% 1.57/0.57    ~spl3_59 | spl3_49 | ~spl3_58),
% 1.57/0.57    inference(avatar_split_clause,[],[f497,f485,f409,f499])).
% 1.57/0.57  fof(f409,plain,(
% 1.57/0.57    spl3_49 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.57/0.57  fof(f485,plain,(
% 1.57/0.57    spl3_58 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.57/0.57  fof(f497,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (spl3_49 | ~spl3_58)),
% 1.57/0.57    inference(backward_demodulation,[],[f411,f487])).
% 1.57/0.57  fof(f487,plain,(
% 1.57/0.57    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_58),
% 1.57/0.57    inference(avatar_component_clause,[],[f485])).
% 1.57/0.57  fof(f411,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_49),
% 1.57/0.57    inference(avatar_component_clause,[],[f409])).
% 1.57/0.57  fof(f496,plain,(
% 1.57/0.57    ~spl3_9 | ~spl3_5 | ~spl3_39 | ~spl3_38 | ~spl3_42 | spl3_57),
% 1.57/0.57    inference(avatar_split_clause,[],[f495,f481,f328,f308,f313,f99,f119])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    spl3_5 <=> v2_funct_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.57/0.57  fof(f328,plain,(
% 1.57/0.57    spl3_42 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.57/0.57  fof(f481,plain,(
% 1.57/0.57    spl3_57 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.57/0.57  fof(f495,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_42 | spl3_57)),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f494])).
% 1.57/0.57  fof(f494,plain,(
% 1.57/0.57    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_42 | spl3_57)),
% 1.57/0.57    inference(forward_demodulation,[],[f492,f330])).
% 1.57/0.57  fof(f330,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_42),
% 1.57/0.57    inference(avatar_component_clause,[],[f328])).
% 1.57/0.57  fof(f492,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | spl3_57),
% 1.57/0.57    inference(resolution,[],[f483,f67])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.57    inference(flattening,[],[f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.57/0.57  fof(f483,plain,(
% 1.57/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | spl3_57),
% 1.57/0.57    inference(avatar_component_clause,[],[f481])).
% 1.57/0.57  fof(f488,plain,(
% 1.57/0.57    ~spl3_46 | ~spl3_44 | ~spl3_57 | ~spl3_45 | spl3_58 | ~spl3_22 | ~spl3_56),
% 1.57/0.57    inference(avatar_split_clause,[],[f479,f464,f197,f485,f359,f481,f346,f375])).
% 1.57/0.57  fof(f375,plain,(
% 1.57/0.57    spl3_46 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.57/0.57  fof(f346,plain,(
% 1.57/0.57    spl3_44 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.57/0.57  fof(f359,plain,(
% 1.57/0.57    spl3_45 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.57/0.57  fof(f197,plain,(
% 1.57/0.57    spl3_22 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.57/0.57  fof(f464,plain,(
% 1.57/0.57    spl3_56 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.57/0.57  fof(f479,plain,(
% 1.57/0.57    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_22 | ~spl3_56)),
% 1.57/0.57    inference(forward_demodulation,[],[f475,f199])).
% 1.57/0.57  fof(f199,plain,(
% 1.57/0.57    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_22),
% 1.57/0.57    inference(avatar_component_clause,[],[f197])).
% 1.57/0.57  fof(f475,plain,(
% 1.57/0.57    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_56),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f470])).
% 1.57/0.57  fof(f470,plain,(
% 1.57/0.57    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_56),
% 1.57/0.57    inference(superposition,[],[f68,f466])).
% 1.57/0.57  fof(f466,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_56),
% 1.57/0.57    inference(avatar_component_clause,[],[f464])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.57    inference(flattening,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.57/0.57  fof(f467,plain,(
% 1.57/0.57    ~spl3_9 | ~spl3_38 | ~spl3_5 | ~spl3_39 | spl3_56 | ~spl3_25 | ~spl3_42),
% 1.57/0.57    inference(avatar_split_clause,[],[f462,f328,f223,f464,f313,f99,f308,f119])).
% 1.57/0.57  fof(f223,plain,(
% 1.57/0.57    spl3_25 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.57/0.57  fof(f462,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_25 | ~spl3_42)),
% 1.57/0.57    inference(forward_demodulation,[],[f461,f225])).
% 1.57/0.57  fof(f225,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_25),
% 1.57/0.57    inference(avatar_component_clause,[],[f223])).
% 1.57/0.57  fof(f461,plain,(
% 1.57/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f460])).
% 1.57/0.57  fof(f460,plain,(
% 1.57/0.57    k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(superposition,[],[f368,f330])).
% 1.57/0.57  fof(f368,plain,(
% 1.57/0.57    ( ! [X6,X8,X7] : (k2_relset_1(X7,X8,X6) != X8 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v2_funct_1(X6) | ~v1_funct_2(X6,X7,X8) | ~v1_funct_1(X6) | k2_relset_1(X8,X7,k2_funct_1(X6)) = k2_relat_1(k2_funct_1(X6))) )),
% 1.57/0.57    inference(resolution,[],[f67,f58])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.57  fof(f412,plain,(
% 1.57/0.57    ~spl3_49 | spl3_40 | ~spl3_48),
% 1.57/0.57    inference(avatar_split_clause,[],[f407,f403,f318,f409])).
% 1.57/0.57  fof(f318,plain,(
% 1.57/0.57    spl3_40 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.57/0.57  fof(f403,plain,(
% 1.57/0.57    spl3_48 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.57/0.57  fof(f407,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_40 | ~spl3_48)),
% 1.57/0.57    inference(backward_demodulation,[],[f320,f405])).
% 1.57/0.57  fof(f405,plain,(
% 1.57/0.57    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_48),
% 1.57/0.57    inference(avatar_component_clause,[],[f403])).
% 1.57/0.57  fof(f320,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_40),
% 1.57/0.57    inference(avatar_component_clause,[],[f318])).
% 1.57/0.57  fof(f406,plain,(
% 1.57/0.57    spl3_48 | ~spl3_5 | ~spl3_9 | ~spl3_39 | ~spl3_38 | ~spl3_42),
% 1.57/0.57    inference(avatar_split_clause,[],[f401,f328,f308,f313,f119,f99,f403])).
% 1.57/0.57  fof(f401,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_42),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f400])).
% 1.57/0.57  fof(f400,plain,(
% 1.57/0.57    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_42),
% 1.57/0.57    inference(superposition,[],[f68,f330])).
% 1.57/0.57  fof(f385,plain,(
% 1.57/0.57    ~spl3_23 | ~spl3_5 | ~spl3_9 | spl3_46),
% 1.57/0.57    inference(avatar_split_clause,[],[f383,f375,f119,f99,f201])).
% 1.57/0.57  fof(f201,plain,(
% 1.57/0.57    spl3_23 <=> v1_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.57/0.57  fof(f383,plain,(
% 1.57/0.57    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_46),
% 1.57/0.57    inference(resolution,[],[f377,f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.57/0.57  fof(f377,plain,(
% 1.57/0.57    ~v2_funct_1(k2_funct_1(sK2)) | spl3_46),
% 1.57/0.57    inference(avatar_component_clause,[],[f375])).
% 1.57/0.57  fof(f363,plain,(
% 1.57/0.57    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 != k2_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.57  fof(f362,plain,(
% 1.57/0.57    spl3_45 | ~spl3_9 | ~spl3_5 | ~spl3_39 | ~spl3_38 | ~spl3_42),
% 1.57/0.57    inference(avatar_split_clause,[],[f357,f328,f308,f313,f99,f119,f359])).
% 1.57/0.57  fof(f357,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f356])).
% 1.57/0.57  fof(f356,plain,(
% 1.57/0.57    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(superposition,[],[f66,f330])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f349,plain,(
% 1.57/0.57    spl3_44 | ~spl3_9 | ~spl3_5 | ~spl3_39 | ~spl3_38 | ~spl3_42),
% 1.57/0.57    inference(avatar_split_clause,[],[f344,f328,f308,f313,f99,f119,f346])).
% 1.57/0.57  fof(f344,plain,(
% 1.57/0.57    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(trivial_inequality_removal,[],[f343])).
% 1.57/0.57  fof(f343,plain,(
% 1.57/0.57    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_42),
% 1.57/0.57    inference(superposition,[],[f65,f330])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f331,plain,(
% 1.57/0.57    spl3_42 | ~spl3_35 | ~spl3_37),
% 1.57/0.57    inference(avatar_split_clause,[],[f305,f297,f283,f328])).
% 1.57/0.57  fof(f283,plain,(
% 1.57/0.57    spl3_35 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.57/0.57  fof(f297,plain,(
% 1.57/0.57    spl3_37 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.57/0.57  fof(f305,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_35 | ~spl3_37)),
% 1.57/0.57    inference(backward_demodulation,[],[f285,f299])).
% 1.57/0.57  fof(f299,plain,(
% 1.57/0.57    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_37),
% 1.57/0.57    inference(avatar_component_clause,[],[f297])).
% 1.57/0.57  fof(f285,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_35),
% 1.57/0.57    inference(avatar_component_clause,[],[f283])).
% 1.57/0.57  fof(f321,plain,(
% 1.57/0.57    ~spl3_40 | spl3_32 | ~spl3_37),
% 1.57/0.57    inference(avatar_split_clause,[],[f303,f297,f268,f318])).
% 1.57/0.57  fof(f268,plain,(
% 1.57/0.57    spl3_32 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.57/0.57  fof(f303,plain,(
% 1.57/0.57    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_32 | ~spl3_37)),
% 1.57/0.57    inference(backward_demodulation,[],[f270,f299])).
% 1.57/0.57  fof(f270,plain,(
% 1.57/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | spl3_32),
% 1.57/0.57    inference(avatar_component_clause,[],[f268])).
% 1.57/0.57  fof(f316,plain,(
% 1.57/0.57    spl3_39 | ~spl3_31 | ~spl3_37),
% 1.57/0.57    inference(avatar_split_clause,[],[f302,f297,f263,f313])).
% 1.57/0.57  fof(f263,plain,(
% 1.57/0.57    spl3_31 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.57/0.57  fof(f302,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_31 | ~spl3_37)),
% 1.57/0.57    inference(backward_demodulation,[],[f265,f299])).
% 1.57/0.57  fof(f265,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_31),
% 1.57/0.57    inference(avatar_component_clause,[],[f263])).
% 1.57/0.57  fof(f311,plain,(
% 1.57/0.57    spl3_38 | ~spl3_30 | ~spl3_37),
% 1.57/0.57    inference(avatar_split_clause,[],[f301,f297,f258,f308])).
% 1.57/0.57  fof(f258,plain,(
% 1.57/0.57    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.57/0.57  fof(f301,plain,(
% 1.57/0.57    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_30 | ~spl3_37)),
% 1.57/0.57    inference(backward_demodulation,[],[f260,f299])).
% 1.57/0.57  fof(f260,plain,(
% 1.57/0.57    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 1.57/0.57    inference(avatar_component_clause,[],[f258])).
% 1.57/0.57  fof(f300,plain,(
% 1.57/0.57    ~spl3_30 | spl3_36 | spl3_37 | ~spl3_31 | ~spl3_34),
% 1.57/0.57    inference(avatar_split_clause,[],[f291,f278,f263,f297,f293,f258])).
% 1.57/0.57  fof(f293,plain,(
% 1.57/0.57    spl3_36 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.57/0.57  fof(f278,plain,(
% 1.57/0.57    spl3_34 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.57/0.57  fof(f291,plain,(
% 1.57/0.57    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_31 | ~spl3_34)),
% 1.57/0.57    inference(forward_demodulation,[],[f290,f280])).
% 1.57/0.57  fof(f280,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_34),
% 1.57/0.57    inference(avatar_component_clause,[],[f278])).
% 1.57/0.57  fof(f290,plain,(
% 1.57/0.57    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_31),
% 1.57/0.57    inference(resolution,[],[f64,f265])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(flattening,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.57/0.57  fof(f286,plain,(
% 1.57/0.57    spl3_35 | ~spl3_27 | ~spl3_28),
% 1.57/0.57    inference(avatar_split_clause,[],[f251,f241,f235,f283])).
% 1.57/0.57  fof(f235,plain,(
% 1.57/0.57    spl3_27 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.57/0.57  fof(f241,plain,(
% 1.57/0.57    spl3_28 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.57/0.57  fof(f251,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_27 | ~spl3_28)),
% 1.57/0.57    inference(backward_demodulation,[],[f237,f243])).
% 1.57/0.57  fof(f243,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_28),
% 1.57/0.57    inference(avatar_component_clause,[],[f241])).
% 1.57/0.57  fof(f237,plain,(
% 1.57/0.57    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_27),
% 1.57/0.57    inference(avatar_component_clause,[],[f235])).
% 1.57/0.57  fof(f281,plain,(
% 1.57/0.57    spl3_34 | ~spl3_26 | ~spl3_28),
% 1.57/0.57    inference(avatar_split_clause,[],[f250,f241,f229,f278])).
% 1.57/0.57  fof(f229,plain,(
% 1.57/0.57    spl3_26 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.57/0.57  fof(f250,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_26 | ~spl3_28)),
% 1.57/0.57    inference(backward_demodulation,[],[f231,f243])).
% 1.57/0.57  fof(f231,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_26),
% 1.57/0.57    inference(avatar_component_clause,[],[f229])).
% 1.57/0.57  fof(f271,plain,(
% 1.57/0.57    ~spl3_32 | spl3_20 | ~spl3_28),
% 1.57/0.57    inference(avatar_split_clause,[],[f248,f241,f184,f268])).
% 1.57/0.57  fof(f184,plain,(
% 1.57/0.57    spl3_20 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.57/0.57  fof(f248,plain,(
% 1.57/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | (spl3_20 | ~spl3_28)),
% 1.57/0.57    inference(backward_demodulation,[],[f186,f243])).
% 1.57/0.57  fof(f186,plain,(
% 1.57/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_20),
% 1.57/0.57    inference(avatar_component_clause,[],[f184])).
% 1.57/0.57  fof(f266,plain,(
% 1.57/0.57    spl3_31 | ~spl3_18 | ~spl3_28),
% 1.57/0.57    inference(avatar_split_clause,[],[f247,f241,f172,f263])).
% 1.57/0.57  fof(f172,plain,(
% 1.57/0.57    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.57/0.57  fof(f247,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_18 | ~spl3_28)),
% 1.57/0.57    inference(backward_demodulation,[],[f174,f243])).
% 1.57/0.57  fof(f174,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_18),
% 1.57/0.57    inference(avatar_component_clause,[],[f172])).
% 1.57/0.57  fof(f261,plain,(
% 1.57/0.57    spl3_30 | ~spl3_17 | ~spl3_28),
% 1.57/0.57    inference(avatar_split_clause,[],[f246,f241,f166,f258])).
% 1.57/0.57  fof(f166,plain,(
% 1.57/0.57    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.57/0.57  fof(f246,plain,(
% 1.57/0.57    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_17 | ~spl3_28)),
% 1.57/0.57    inference(backward_demodulation,[],[f168,f243])).
% 1.57/0.57  fof(f168,plain,(
% 1.57/0.57    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_17),
% 1.57/0.57    inference(avatar_component_clause,[],[f166])).
% 1.57/0.57  fof(f244,plain,(
% 1.57/0.57    spl3_28 | ~spl3_19 | ~spl3_27),
% 1.57/0.57    inference(avatar_split_clause,[],[f239,f235,f178,f241])).
% 1.57/0.57  fof(f178,plain,(
% 1.57/0.57    spl3_19 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.57/0.57  fof(f239,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_19 | ~spl3_27)),
% 1.57/0.57    inference(backward_demodulation,[],[f180,f237])).
% 1.57/0.57  fof(f180,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_19),
% 1.57/0.57    inference(avatar_component_clause,[],[f178])).
% 1.57/0.57  fof(f238,plain,(
% 1.57/0.57    spl3_27 | ~spl3_18),
% 1.57/0.57    inference(avatar_split_clause,[],[f233,f172,f235])).
% 1.57/0.57  fof(f233,plain,(
% 1.57/0.57    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_18),
% 1.57/0.57    inference(resolution,[],[f58,f174])).
% 1.57/0.57  fof(f232,plain,(
% 1.57/0.57    spl3_26 | ~spl3_18),
% 1.57/0.57    inference(avatar_split_clause,[],[f227,f172,f229])).
% 1.57/0.57  fof(f227,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_18),
% 1.57/0.57    inference(resolution,[],[f57,f174])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.57/0.57  fof(f226,plain,(
% 1.57/0.57    spl3_25 | ~spl3_23 | ~spl3_9 | ~spl3_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f220,f99,f119,f201,f223])).
% 1.57/0.57  fof(f220,plain,(
% 1.57/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.57/0.57    inference(resolution,[],[f55,f101])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    v2_funct_1(sK2) | ~spl3_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f99])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.57/0.57  fof(f209,plain,(
% 1.57/0.57    ~spl3_18 | spl3_23),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f208])).
% 1.57/0.57  fof(f208,plain,(
% 1.57/0.57    $false | (~spl3_18 | spl3_23)),
% 1.57/0.57    inference(subsumption_resolution,[],[f174,f206])).
% 1.57/0.57  fof(f206,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_23),
% 1.57/0.57    inference(resolution,[],[f203,f56])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.57  fof(f203,plain,(
% 1.57/0.57    ~v1_relat_1(sK2) | spl3_23),
% 1.57/0.57    inference(avatar_component_clause,[],[f201])).
% 1.57/0.57  fof(f204,plain,(
% 1.57/0.57    spl3_22 | ~spl3_23 | ~spl3_9 | ~spl3_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f194,f99,f119,f201,f197])).
% 1.57/0.57  fof(f194,plain,(
% 1.57/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.57/0.57    inference(resolution,[],[f53,f101])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.57/0.57  fof(f193,plain,(
% 1.57/0.57    ~spl3_21 | ~spl3_2 | spl3_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f188,f89,f84,f190])).
% 1.57/0.57  fof(f190,plain,(
% 1.57/0.57    spl3_21 <=> v1_xboole_0(k2_struct_0(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    spl3_2 <=> l1_struct_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    spl3_3 <=> v2_struct_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.57  fof(f188,plain,(
% 1.57/0.57    ~l1_struct_0(sK1) | ~v1_xboole_0(k2_struct_0(sK1)) | spl3_3),
% 1.57/0.57    inference(resolution,[],[f49,f91])).
% 1.57/0.57  fof(f91,plain,(
% 1.57/0.57    ~v2_struct_0(sK1) | spl3_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f89])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.57/0.57  fof(f187,plain,(
% 1.57/0.57    ~spl3_20 | ~spl3_11 | spl3_13),
% 1.57/0.57    inference(avatar_split_clause,[],[f182,f145,f131,f184])).
% 1.57/0.57  fof(f131,plain,(
% 1.57/0.57    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.57/0.57  fof(f145,plain,(
% 1.57/0.57    spl3_13 <=> r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.57/0.57  fof(f182,plain,(
% 1.57/0.57    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_11 | spl3_13)),
% 1.57/0.57    inference(forward_demodulation,[],[f147,f133])).
% 1.57/0.57  fof(f133,plain,(
% 1.57/0.57    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 1.57/0.57    inference(avatar_component_clause,[],[f131])).
% 1.57/0.57  fof(f147,plain,(
% 1.57/0.57    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 1.57/0.57    inference(avatar_component_clause,[],[f145])).
% 1.57/0.57  fof(f181,plain,(
% 1.57/0.57    spl3_19 | ~spl3_11 | ~spl3_14),
% 1.57/0.57    inference(avatar_split_clause,[],[f176,f150,f131,f178])).
% 1.57/0.57  fof(f150,plain,(
% 1.57/0.57    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.57/0.57  fof(f176,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_11 | ~spl3_14)),
% 1.57/0.57    inference(forward_demodulation,[],[f152,f133])).
% 1.57/0.57  fof(f152,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 1.57/0.57    inference(avatar_component_clause,[],[f150])).
% 1.57/0.57  fof(f175,plain,(
% 1.57/0.57    spl3_18 | ~spl3_11 | ~spl3_15),
% 1.57/0.57    inference(avatar_split_clause,[],[f170,f155,f131,f172])).
% 1.57/0.57  fof(f155,plain,(
% 1.57/0.57    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.57/0.57  fof(f170,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_11 | ~spl3_15)),
% 1.57/0.57    inference(forward_demodulation,[],[f157,f133])).
% 1.57/0.57  fof(f157,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 1.57/0.57    inference(avatar_component_clause,[],[f155])).
% 1.57/0.57  fof(f169,plain,(
% 1.57/0.57    spl3_17 | ~spl3_11 | ~spl3_16),
% 1.57/0.57    inference(avatar_split_clause,[],[f164,f160,f131,f166])).
% 1.57/0.57  fof(f160,plain,(
% 1.57/0.57    spl3_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.57/0.57  fof(f164,plain,(
% 1.57/0.57    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_11 | ~spl3_16)),
% 1.57/0.57    inference(forward_demodulation,[],[f162,f133])).
% 1.57/0.57  fof(f162,plain,(
% 1.57/0.57    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 1.57/0.57    inference(avatar_component_clause,[],[f160])).
% 1.57/0.57  fof(f163,plain,(
% 1.57/0.57    spl3_16 | ~spl3_8 | ~spl3_12),
% 1.57/0.57    inference(avatar_split_clause,[],[f143,f136,f114,f160])).
% 1.57/0.57  fof(f114,plain,(
% 1.57/0.57    spl3_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.57/0.57  fof(f136,plain,(
% 1.57/0.57    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.57/0.57  fof(f143,plain,(
% 1.57/0.57    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_8 | ~spl3_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f116,f138])).
% 1.57/0.57  fof(f138,plain,(
% 1.57/0.57    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f136])).
% 1.57/0.57  fof(f116,plain,(
% 1.57/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f114])).
% 1.57/0.57  fof(f158,plain,(
% 1.57/0.57    spl3_15 | ~spl3_7 | ~spl3_12),
% 1.57/0.57    inference(avatar_split_clause,[],[f142,f136,f109,f155])).
% 1.57/0.57  fof(f109,plain,(
% 1.57/0.57    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.57/0.57  fof(f142,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f111,f138])).
% 1.57/0.57  fof(f111,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f109])).
% 1.57/0.57  fof(f153,plain,(
% 1.57/0.57    spl3_14 | ~spl3_6 | ~spl3_12),
% 1.57/0.57    inference(avatar_split_clause,[],[f141,f136,f104,f150])).
% 1.57/0.57  fof(f104,plain,(
% 1.57/0.57    spl3_6 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.57/0.57  fof(f141,plain,(
% 1.57/0.57    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f106,f138])).
% 1.57/0.57  fof(f106,plain,(
% 1.57/0.57    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl3_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f104])).
% 1.57/0.57  fof(f148,plain,(
% 1.57/0.57    ~spl3_13 | spl3_4 | ~spl3_12),
% 1.57/0.57    inference(avatar_split_clause,[],[f140,f136,f94,f145])).
% 1.57/0.57  fof(f94,plain,(
% 1.57/0.57    spl3_4 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.57  fof(f140,plain,(
% 1.57/0.57    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_4 | ~spl3_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f96,f138])).
% 1.57/0.57  fof(f96,plain,(
% 1.57/0.57    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f94])).
% 1.57/0.57  fof(f139,plain,(
% 1.57/0.57    spl3_12 | ~spl3_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f129,f84,f136])).
% 1.57/0.57  fof(f129,plain,(
% 1.57/0.57    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_2),
% 1.57/0.57    inference(resolution,[],[f48,f86])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    l1_struct_0(sK1) | ~spl3_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f84])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.57/0.57  fof(f134,plain,(
% 1.57/0.57    spl3_11 | ~spl3_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f128,f79,f131])).
% 1.57/0.57  fof(f79,plain,(
% 1.57/0.57    spl3_1 <=> l1_struct_0(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.57/0.57  fof(f128,plain,(
% 1.57/0.57    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_1),
% 1.57/0.57    inference(resolution,[],[f48,f81])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    l1_struct_0(sK0) | ~spl3_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f79])).
% 1.57/0.57  % (31348)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.57  fof(f127,plain,(
% 1.57/0.57    spl3_10),
% 1.57/0.57    inference(avatar_split_clause,[],[f47,f124])).
% 1.57/0.57  fof(f124,plain,(
% 1.57/0.57    spl3_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    spl3_9),
% 1.57/0.57    inference(avatar_split_clause,[],[f38,f119])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    v1_funct_1(sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f16])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,negated_conjecture,(
% 1.57/0.57    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.57/0.57    inference(negated_conjecture,[],[f14])).
% 1.57/0.57  fof(f14,conjecture,(
% 1.57/0.57    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.57/0.57  fof(f117,plain,(
% 1.57/0.57    spl3_8),
% 1.57/0.57    inference(avatar_split_clause,[],[f39,f114])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    spl3_7),
% 1.57/0.57    inference(avatar_split_clause,[],[f40,f109])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    spl3_6),
% 1.57/0.57    inference(avatar_split_clause,[],[f41,f104])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f102,plain,(
% 1.57/0.57    spl3_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f42,f99])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    v2_funct_1(sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f97,plain,(
% 1.57/0.57    ~spl3_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f43,f94])).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f92,plain,(
% 1.57/0.57    ~spl3_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f44,f89])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ~v2_struct_0(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f87,plain,(
% 1.57/0.57    spl3_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f45,f84])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    l1_struct_0(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f82,plain,(
% 1.57/0.57    spl3_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f46,f79])).
% 1.57/0.57  fof(f46,plain,(
% 1.57/0.57    l1_struct_0(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (31362)------------------------------
% 1.57/0.57  % (31362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (31362)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (31362)Memory used [KB]: 6652
% 1.57/0.57  % (31362)Time elapsed: 0.136 s
% 1.57/0.57  % (31362)------------------------------
% 1.57/0.57  % (31362)------------------------------
% 1.57/0.57  % (31360)Refutation not found, incomplete strategy% (31360)------------------------------
% 1.57/0.57  % (31360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (31360)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (31360)Memory used [KB]: 6652
% 1.57/0.57  % (31360)Time elapsed: 0.158 s
% 1.57/0.57  % (31360)------------------------------
% 1.57/0.57  % (31360)------------------------------
% 1.57/0.57  % (31346)Success in time 0.213 s
%------------------------------------------------------------------------------
