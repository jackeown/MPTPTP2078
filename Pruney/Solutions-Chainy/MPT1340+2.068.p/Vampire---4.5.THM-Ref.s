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
% DateTime   : Thu Dec  3 13:14:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  288 ( 597 expanded)
%              Number of leaves         :   66 ( 284 expanded)
%              Depth                    :   17
%              Number of atoms          : 1159 (2487 expanded)
%              Number of equality atoms :  182 ( 420 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f96,f100,f104,f108,f112,f116,f120,f124,f130,f134,f147,f149,f154,f159,f165,f192,f201,f205,f233,f244,f258,f276,f280,f292,f322,f335,f365,f389,f392,f406,f420,f432,f440,f464,f480,f488,f493,f513,f527,f535,f545,f550,f556,f559])).

fof(f559,plain,
    ( ~ spl3_49
    | ~ spl3_6
    | ~ spl3_47
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f557,f554,f423,f110,f438])).

fof(f438,plain,
    ( spl3_49
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f110,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f423,plain,
    ( spl3_47
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f554,plain,
    ( spl3_59
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f557,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_47
    | ~ spl3_59 ),
    inference(resolution,[],[f555,f424])).

fof(f424,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f423])).

fof(f555,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f554])).

fof(f556,plain,
    ( ~ spl3_6
    | ~ spl3_47
    | ~ spl3_49
    | spl3_59
    | spl3_58 ),
    inference(avatar_split_clause,[],[f552,f543,f554,f438,f423,f110])).

fof(f543,plain,
    ( spl3_58
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | spl3_58 ),
    inference(resolution,[],[f544,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

% (11020)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f544,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_58 ),
    inference(avatar_component_clause,[],[f543])).

fof(f550,plain,
    ( ~ spl3_49
    | ~ spl3_47
    | ~ spl3_38
    | ~ spl3_45
    | ~ spl3_50
    | spl3_57 ),
    inference(avatar_split_clause,[],[f549,f540,f462,f398,f333,f423,f438])).

fof(f333,plain,
    ( spl3_38
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f398,plain,
    ( spl3_45
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f462,plain,
    ( spl3_50
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f540,plain,
    ( spl3_57
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f549,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_38
    | ~ spl3_45
    | ~ spl3_50
    | spl3_57 ),
    inference(trivial_inequality_removal,[],[f548])).

fof(f548,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_38
    | ~ spl3_45
    | ~ spl3_50
    | spl3_57 ),
    inference(forward_demodulation,[],[f547,f399])).

fof(f399,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f398])).

fof(f547,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_38
    | ~ spl3_50
    | spl3_57 ),
    inference(trivial_inequality_removal,[],[f546])).

fof(f546,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_38
    | ~ spl3_50
    | spl3_57 ),
    inference(superposition,[],[f541,f473])).

fof(f473,plain,
    ( ! [X4,X3] :
        ( k1_relat_1(sK2) = k2_relset_1(X4,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(sK2,X3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_relset_1(X3,X4,sK2) != X4 )
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f472,f334])).

fof(f334,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f333])).

fof(f472,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_2(sK2,X3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_relset_1(X3,X4,sK2) != X4
        | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(X4,X3,k2_funct_1(sK2)) )
    | ~ spl3_50 ),
    inference(resolution,[],[f463,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f463,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f462])).

fof(f541,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f540])).

fof(f545,plain,
    ( ~ spl3_57
    | ~ spl3_47
    | ~ spl3_49
    | ~ spl3_58
    | ~ spl3_45
    | spl3_55
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f538,f533,f525,f398,f543,f438,f423,f540])).

% (11024)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f525,plain,
    ( spl3_55
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f533,plain,
    ( spl3_56
  <=> ! [X1,X0] :
        ( sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f538,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_45
    | spl3_55
    | ~ spl3_56 ),
    inference(trivial_inequality_removal,[],[f537])).

fof(f537,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_45
    | spl3_55
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f536,f399])).

fof(f536,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_55
    | ~ spl3_56 ),
    inference(superposition,[],[f526,f534])).

fof(f534,plain,
    ( ! [X0,X1] :
        ( sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f533])).

fof(f526,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_55 ),
    inference(avatar_component_clause,[],[f525])).

fof(f535,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_56
    | ~ spl3_50
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f530,f491,f462,f533,f94,f110])).

fof(f94,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f491,plain,
    ( spl3_53
  <=> ! [X5,X6] :
        ( sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X5,X6)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f530,plain,
    ( ! [X0,X1] :
        ( sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_50
    | ~ spl3_53 ),
    inference(duplicate_literal_removal,[],[f529])).

fof(f529,plain,
    ( ! [X0,X1] :
        ( sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_50
    | ~ spl3_53 ),
    inference(resolution,[],[f528,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
        | sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2))
        | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0 )
    | ~ spl3_50
    | ~ spl3_53 ),
    inference(resolution,[],[f492,f463])).

fof(f492,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k2_funct_1(sK2),X5,X6)
        | sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2))
        | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6 )
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f491])).

fof(f527,plain,
    ( ~ spl3_55
    | spl3_46
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f523,f511,f418,f525])).

fof(f418,plain,
    ( spl3_46
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f511,plain,
    ( spl3_54
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f523,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_46
    | ~ spl3_54 ),
    inference(superposition,[],[f419,f512])).

fof(f512,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f511])).

fof(f419,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f418])).

fof(f513,plain,
    ( ~ spl3_47
    | spl3_54
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f509,f486,f382,f247,f132,f128,f102,f98,f511,f423])).

fof(f98,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f132,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f247,plain,
    ( spl3_28
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f382,plain,
    ( spl3_43
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f486,plain,
    ( spl3_52
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f509,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f508])).

fof(f508,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f507,f248])).

fof(f248,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f247])).

fof(f507,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f506,f129])).

fof(f129,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f506,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f505,f248])).

fof(f505,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f504,f99])).

fof(f99,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f504,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f503,f383])).

fof(f383,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f382])).

fof(f503,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f502,f133])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f502,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f501,f248])).

fof(f501,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f500,f129])).

fof(f500,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_43
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f499,f383])).

fof(f499,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_28
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f498,f133])).

fof(f498,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_28
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f497,f248])).

fof(f497,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f494,f129])).

fof(f494,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_52 ),
    inference(resolution,[],[f487,f103])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f487,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f486])).

fof(f493,plain,
    ( ~ spl3_23
    | spl3_53
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f489,f285,f190,f491,f212])).

fof(f212,plain,
    ( spl3_23
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f190,plain,
    ( spl3_20
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f285,plain,
    ( spl3_35
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f489,plain,
    ( ! [X6,X5] :
        ( sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2))
        | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k2_funct_1(sK2),X5,X6)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f484,f191])).

fof(f191,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f484,plain,
    ( ! [X6,X5] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X5,X6,k2_funct_1(sK2))
        | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k2_funct_1(sK2),X5,X6)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_35 ),
    inference(resolution,[],[f86,f321])).

fof(f321,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f285])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

% (11030)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f488,plain,
    ( ~ spl3_6
    | spl3_52
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f482,f94,f486,f110])).

fof(f482,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f86,f95])).

fof(f95,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f480,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f464,plain,
    ( ~ spl3_6
    | spl3_50
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f458,f94,f462,f110])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f85,f95])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f440,plain,
    ( spl3_49
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f435,f382,f270,f438])).

fof(f270,plain,
    ( spl3_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f435,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(superposition,[],[f271,f383])).

fof(f271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f432,plain,
    ( spl3_47
    | ~ spl3_33
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f414,f382,f274,f423])).

fof(f274,plain,
    ( spl3_33
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f414,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_33
    | ~ spl3_43 ),
    inference(superposition,[],[f275,f383])).

fof(f275,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f274])).

fof(f420,plain,
    ( ~ spl3_46
    | spl3_13
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f416,f382,f247,f145,f418])).

fof(f145,plain,
    ( spl3_13
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f416,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_13
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f409,f248])).

fof(f409,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13
    | ~ spl3_43 ),
    inference(superposition,[],[f146,f383])).

fof(f146,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f406,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f405,f247,f152,f270])).

fof(f152,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f405,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f153,f248])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f392,plain,
    ( ~ spl3_14
    | ~ spl3_42 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f153,f379])).

fof(f379,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl3_42
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f389,plain,
    ( spl3_34
    | spl3_43
    | ~ spl3_33
    | spl3_42
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f369,f363,f270,f378,f274,f382,f278])).

fof(f278,plain,
    ( spl3_34
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f363,plain,
    ( spl3_41
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f369,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2)))
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | v1_xboole_0(k2_relat_1(sK2)) )
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(resolution,[],[f364,f271])).

fof(f364,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | v1_xboole_0(X1) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f363])).

fof(f365,plain,
    ( ~ spl3_19
    | spl3_41
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f359,f110,f363,f186])).

fof(f186,plain,
    ( spl3_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f359,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | k1_relat_1(sK2) = X0
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl3_6 ),
    inference(resolution,[],[f349,f111])).

% (11028)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f111,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f349,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(X2)
      | k1_relat_1(X0) = X1
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(resolution,[],[f306,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f306,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(X2)
      | k1_relat_1(X0) = X1
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f335,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | spl3_38
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f331,f285,f190,f333,f212,f209])).

fof(f209,plain,
    ( spl3_22
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f331,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f328,f191])).

fof(f328,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_35 ),
    inference(resolution,[],[f321,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f322,plain,
    ( spl3_35
    | ~ spl3_19
    | ~ spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f319,f94,f110,f186,f285])).

fof(f319,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f317,f95])).

fof(f317,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f311,f63])).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f311,plain,(
    ! [X1] :
      ( ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
      | v2_funct_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1) ) ),
    inference(global_subsumption,[],[f68,f67,f71,f309])).

fof(f309,plain,(
    ! [X1] :
      ( ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
      | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
      | v2_funct_1(k2_funct_1(X1))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X1] :
      ( ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
      | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
      | v2_funct_1(k2_funct_1(X1))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f74,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_23 ),
    inference(avatar_split_clause,[],[f291,f212,f110,f186])).

fof(f291,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(resolution,[],[f213,f68])).

fof(f213,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f280,plain,
    ( ~ spl3_34
    | spl3_16
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f263,f247,f163,f278])).

fof(f163,plain,
    ( spl3_16
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f263,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_16
    | ~ spl3_28 ),
    inference(superposition,[],[f164,f248])).

fof(f164,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f276,plain,
    ( spl3_33
    | ~ spl3_15
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f262,f247,f157,f274])).

fof(f157,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f262,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_28 ),
    inference(superposition,[],[f158,f248])).

fof(f158,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f258,plain,
    ( spl3_28
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f256,f242,f136,f247])).

fof(f136,plain,
    ( spl3_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f242,plain,
    ( spl3_27
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f256,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(superposition,[],[f137,f243])).

fof(f243,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f242])).

fof(f137,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f244,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f240,f132,f128,f102,f242])).

fof(f240,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f239,f133])).

fof(f239,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f237,f129])).

fof(f237,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f81,f103])).

fof(f233,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_22 ),
    inference(avatar_split_clause,[],[f231,f209,f110,f186])).

fof(f231,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_22 ),
    inference(resolution,[],[f210,f67])).

fof(f210,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f209])).

fof(f205,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_21 ),
    inference(resolution,[],[f200,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f200,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_21
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f201,plain,
    ( ~ spl3_21
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_19 ),
    inference(avatar_split_clause,[],[f197,f186,f132,f128,f102,f199])).

fof(f197,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_19 ),
    inference(forward_demodulation,[],[f196,f133])).

fof(f196,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | spl3_19 ),
    inference(forward_demodulation,[],[f194,f129])).

fof(f194,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl3_4
    | spl3_19 ),
    inference(resolution,[],[f193,f103])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_19 ),
    inference(resolution,[],[f187,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f187,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f192,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_20
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f183,f94,f190,f110,f186])).

fof(f183,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f95])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f165,plain,
    ( spl3_8
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f142,f128,f163,f114,f118])).

fof(f118,plain,
    ( spl3_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f114,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f142,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f66,f129])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f159,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f155,f132,f128,f106,f157])).

fof(f106,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f155,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f141,f133])).

fof(f141,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f107,f129])).

fof(f107,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f154,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f150,f132,f128,f102,f152])).

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f140,f133])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f103,f129])).

fof(f149,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f148,f132,f128,f98,f136])).

fof(f148,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f139,f133])).

fof(f139,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f99,f129])).

fof(f147,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f143,f132,f128,f90,f145])).

fof(f90,plain,
    ( spl3_1
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f143,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f138,f133])).

fof(f138,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f91,f129])).

fof(f91,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f134,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f126,f122,f132])).

fof(f122,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f126,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f64,f123])).

fof(f123,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f130,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f125,f114,f128])).

fof(f125,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f115])).

fof(f115,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f124,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f54,f122])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

% (11033)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f120,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f55,f118])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f56,f114])).

fof(f56,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f57,f110])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f106])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f102])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f60,f98])).

fof(f60,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f61,f94])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f62,f90])).

fof(f62,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (11034)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (11026)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (11022)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (11037)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (11021)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (11023)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (11025)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (11031)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (11035)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (11040)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (11039)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (11040)Refutation not found, incomplete strategy% (11040)------------------------------
% 0.20/0.49  % (11040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11040)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (11040)Memory used [KB]: 10618
% 0.20/0.49  % (11040)Time elapsed: 0.084 s
% 0.20/0.49  % (11040)------------------------------
% 0.20/0.49  % (11040)------------------------------
% 0.20/0.50  % (11026)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f560,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f92,f96,f100,f104,f108,f112,f116,f120,f124,f130,f134,f147,f149,f154,f159,f165,f192,f201,f205,f233,f244,f258,f276,f280,f292,f322,f335,f365,f389,f392,f406,f420,f432,f440,f464,f480,f488,f493,f513,f527,f535,f545,f550,f556,f559])).
% 0.20/0.50  fof(f559,plain,(
% 0.20/0.50    ~spl3_49 | ~spl3_6 | ~spl3_47 | ~spl3_59),
% 0.20/0.50    inference(avatar_split_clause,[],[f557,f554,f423,f110,f438])).
% 0.20/0.50  fof(f438,plain,(
% 0.20/0.50    spl3_49 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    spl3_47 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    spl3_59 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.50  fof(f557,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_47 | ~spl3_59)),
% 0.20/0.50    inference(resolution,[],[f555,f424])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_47),
% 0.20/0.50    inference(avatar_component_clause,[],[f423])).
% 0.20/0.50  fof(f555,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | ~spl3_59),
% 0.20/0.50    inference(avatar_component_clause,[],[f554])).
% 0.20/0.50  fof(f556,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_47 | ~spl3_49 | spl3_59 | spl3_58),
% 0.20/0.50    inference(avatar_split_clause,[],[f552,f543,f554,f438,f423,f110])).
% 0.20/0.50  fof(f543,plain,(
% 0.20/0.50    spl3_58 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.50  fof(f552,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | spl3_58),
% 0.20/0.50    inference(resolution,[],[f544,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.50  % (11020)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f544,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_58),
% 0.20/0.50    inference(avatar_component_clause,[],[f543])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    ~spl3_49 | ~spl3_47 | ~spl3_38 | ~spl3_45 | ~spl3_50 | spl3_57),
% 0.20/0.50    inference(avatar_split_clause,[],[f549,f540,f462,f398,f333,f423,f438])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl3_38 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    spl3_45 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.50  fof(f462,plain,(
% 0.20/0.50    spl3_50 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    spl3_57 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.50  fof(f549,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_38 | ~spl3_45 | ~spl3_50 | spl3_57)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f548])).
% 0.20/0.50  fof(f548,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_38 | ~spl3_45 | ~spl3_50 | spl3_57)),
% 0.20/0.50    inference(forward_demodulation,[],[f547,f399])).
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_45),
% 0.20/0.50    inference(avatar_component_clause,[],[f398])).
% 0.20/0.50  fof(f547,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_38 | ~spl3_50 | spl3_57)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f546])).
% 0.20/0.50  fof(f546,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_38 | ~spl3_50 | spl3_57)),
% 0.20/0.50    inference(superposition,[],[f541,f473])).
% 0.20/0.50  fof(f473,plain,(
% 0.20/0.50    ( ! [X4,X3] : (k1_relat_1(sK2) = k2_relset_1(X4,X3,k2_funct_1(sK2)) | ~v1_funct_2(sK2,X3,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_relset_1(X3,X4,sK2) != X4) ) | (~spl3_38 | ~spl3_50)),
% 0.20/0.50    inference(forward_demodulation,[],[f472,f334])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl3_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f333])).
% 0.20/0.50  fof(f472,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~v1_funct_2(sK2,X3,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_relset_1(X3,X4,sK2) != X4 | k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(X4,X3,k2_funct_1(sK2))) ) | ~spl3_50),
% 0.20/0.50    inference(resolution,[],[f463,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f462])).
% 0.20/0.50  fof(f541,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_57),
% 0.20/0.50    inference(avatar_component_clause,[],[f540])).
% 0.20/0.50  fof(f545,plain,(
% 0.20/0.50    ~spl3_57 | ~spl3_47 | ~spl3_49 | ~spl3_58 | ~spl3_45 | spl3_55 | ~spl3_56),
% 0.20/0.50    inference(avatar_split_clause,[],[f538,f533,f525,f398,f543,f438,f423,f540])).
% 0.20/0.50  % (11024)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  fof(f525,plain,(
% 0.20/0.50    spl3_55 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.50  fof(f533,plain,(
% 0.20/0.50    spl3_56 <=> ! [X1,X0] : (sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.50  fof(f538,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_45 | spl3_55 | ~spl3_56)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f537])).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_45 | spl3_55 | ~spl3_56)),
% 0.20/0.50    inference(forward_demodulation,[],[f536,f399])).
% 0.20/0.50  fof(f536,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_55 | ~spl3_56)),
% 0.20/0.50    inference(superposition,[],[f526,f534])).
% 0.20/0.50  fof(f534,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1) ) | ~spl3_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f533])).
% 0.20/0.50  fof(f526,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_55),
% 0.20/0.50    inference(avatar_component_clause,[],[f525])).
% 0.20/0.50  fof(f535,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_2 | spl3_56 | ~spl3_50 | ~spl3_53),
% 0.20/0.50    inference(avatar_split_clause,[],[f530,f491,f462,f533,f94,f110])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    spl3_53 <=> ! [X5,X6] : (sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X5,X6) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.50  fof(f530,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | ~v2_funct_1(sK2) | ~v1_funct_1(sK2)) ) | (~spl3_50 | ~spl3_53)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f529])).
% 0.20/0.50  fof(f529,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | k2_relset_1(X1,X0,sK2) != X0 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) ) | (~spl3_50 | ~spl3_53)),
% 0.20/0.50    inference(resolution,[],[f528,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  fof(f528,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_2(k2_funct_1(sK2),X0,X1) | sK2 = k2_tops_2(X0,X1,k2_funct_1(sK2)) | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0) ) | (~spl3_50 | ~spl3_53)),
% 0.20/0.50    inference(resolution,[],[f492,f463])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    ( ! [X6,X5] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k2_funct_1(sK2),X5,X6) | sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2)) | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6) ) | ~spl3_53),
% 0.20/0.50    inference(avatar_component_clause,[],[f491])).
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    ~spl3_55 | spl3_46 | ~spl3_54),
% 0.20/0.50    inference(avatar_split_clause,[],[f523,f511,f418,f525])).
% 0.20/0.50  fof(f418,plain,(
% 0.20/0.50    spl3_46 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.50  fof(f511,plain,(
% 0.20/0.50    spl3_54 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_46 | ~spl3_54)),
% 0.20/0.50    inference(superposition,[],[f419,f512])).
% 0.20/0.50  fof(f512,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f511])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f418])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    ~spl3_47 | spl3_54 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52),
% 0.20/0.50    inference(avatar_split_clause,[],[f509,f486,f382,f247,f132,f128,f102,f98,f511,f423])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    spl3_28 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    spl3_43 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.50  fof(f486,plain,(
% 0.20/0.50    spl3_52 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.50  fof(f509,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f508])).
% 0.20/0.50  fof(f508,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f507,f248])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f247])).
% 0.20/0.50  fof(f507,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f506,f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f128])).
% 0.20/0.50  fof(f506,plain,(
% 0.20/0.50    u1_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f505,f248])).
% 0.20/0.50  fof(f505,plain,(
% 0.20/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f504,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f98])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f503,f383])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f382])).
% 0.20/0.50  fof(f503,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f502,f133])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f132])).
% 0.20/0.50  fof(f502,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f501,f248])).
% 0.20/0.50  fof(f501,plain,(
% 0.20/0.50    k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f500,f129])).
% 0.20/0.50  fof(f500,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_43 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f499,f383])).
% 0.20/0.50  fof(f499,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_28 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f498,f133])).
% 0.20/0.50  fof(f498,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_28 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f497,f248])).
% 0.20/0.50  fof(f497,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f494,f129])).
% 0.20/0.50  fof(f494,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_52)),
% 0.20/0.50    inference(resolution,[],[f487,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f102])).
% 0.20/0.50  fof(f487,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_52),
% 0.20/0.50    inference(avatar_component_clause,[],[f486])).
% 0.20/0.50  fof(f493,plain,(
% 0.20/0.50    ~spl3_23 | spl3_53 | ~spl3_20 | ~spl3_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f489,f285,f190,f491,f212])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    spl3_23 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl3_20 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    spl3_35 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.50  fof(f489,plain,(
% 0.20/0.50    ( ! [X6,X5] : (sK2 = k2_tops_2(X5,X6,k2_funct_1(sK2)) | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k2_funct_1(sK2),X5,X6) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl3_20 | ~spl3_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f484,f191])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f484,plain,(
% 0.20/0.50    ( ! [X6,X5] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X5,X6,k2_funct_1(sK2)) | k2_relset_1(X5,X6,k2_funct_1(sK2)) != X6 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k2_funct_1(sK2),X5,X6) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_35),
% 0.20/0.50    inference(resolution,[],[f86,f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    v2_funct_1(k2_funct_1(sK2)) | ~spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f285])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  % (11030)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  fof(f488,plain,(
% 0.20/0.50    ~spl3_6 | spl3_52 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f482,f94,f486,f110])).
% 0.20/0.50  fof(f482,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f86,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f94])).
% 0.20/0.50  fof(f480,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    ~spl3_6 | spl3_50 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f458,f94,f462,f110])).
% 0.20/0.50  fof(f458,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f85,f95])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f440,plain,(
% 0.20/0.50    spl3_49 | ~spl3_32 | ~spl3_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f435,f382,f270,f438])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    spl3_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_32 | ~spl3_43)),
% 0.20/0.50    inference(superposition,[],[f271,f383])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f270])).
% 0.20/0.50  fof(f432,plain,(
% 0.20/0.50    spl3_47 | ~spl3_33 | ~spl3_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f414,f382,f274,f423])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    spl3_33 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_33 | ~spl3_43)),
% 0.20/0.50    inference(superposition,[],[f275,f383])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f274])).
% 0.20/0.50  fof(f420,plain,(
% 0.20/0.50    ~spl3_46 | spl3_13 | ~spl3_28 | ~spl3_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f416,f382,f247,f145,f418])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl3_13 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_13 | ~spl3_28 | ~spl3_43)),
% 0.20/0.50    inference(forward_demodulation,[],[f409,f248])).
% 0.20/0.50  fof(f409,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2) | (spl3_13 | ~spl3_43)),
% 0.20/0.50    inference(superposition,[],[f146,f383])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f145])).
% 0.20/0.50  fof(f406,plain,(
% 0.20/0.50    spl3_32 | ~spl3_14 | ~spl3_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f405,f247,f152,f270])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.50  fof(f405,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_28)),
% 0.20/0.50    inference(forward_demodulation,[],[f153,f248])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f152])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    ~spl3_14 | ~spl3_42),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f390])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    $false | (~spl3_14 | ~spl3_42)),
% 0.20/0.50    inference(subsumption_resolution,[],[f153,f379])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f378])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    spl3_42 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    spl3_34 | spl3_43 | ~spl3_33 | spl3_42 | ~spl3_32 | ~spl3_41),
% 0.20/0.50    inference(avatar_split_clause,[],[f369,f363,f270,f378,f274,f382,f278])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    spl3_34 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    spl3_41 <=> ! [X1,X0,X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.50  fof(f369,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X2))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK0) = k1_relat_1(sK2) | v1_xboole_0(k2_relat_1(sK2))) ) | (~spl3_32 | ~spl3_41)),
% 0.20/0.50    inference(resolution,[],[f364,f271])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | v1_xboole_0(X1)) ) | ~spl3_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f363])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    ~spl3_19 | spl3_41 | ~spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f359,f110,f363,f186])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    spl3_19 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | k1_relat_1(sK2) = X0 | ~v1_funct_2(sK2,X0,X1) | ~v1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl3_6),
% 0.20/0.50    inference(resolution,[],[f349,f111])).
% 0.20/0.50  % (11028)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl3_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f110])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | k1_relat_1(X0) = X1 | ~v1_funct_2(X0,X1,X2) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.50    inference(resolution,[],[f306,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v4_relat_1(X0,X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | k1_relat_1(X0) = X1 | ~v1_funct_2(X0,X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f78,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    ~spl3_22 | ~spl3_23 | spl3_38 | ~spl3_20 | ~spl3_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f331,f285,f190,f333,f212,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    spl3_22 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_20 | ~spl3_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f328,f191])).
% 0.20/0.50  fof(f328,plain,(
% 0.20/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_35),
% 0.20/0.50    inference(resolution,[],[f321,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    spl3_35 | ~spl3_19 | ~spl3_6 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f319,f94,f110,f186,f285])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f317,f95])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f311,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_funct_1(k6_relat_1(k2_relat_1(X1))) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1)) )),
% 0.20/0.50    inference(global_subsumption,[],[f68,f67,f71,f309])).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_funct_1(k6_relat_1(k2_relat_1(X1))) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f308])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_funct_1(k6_relat_1(k2_relat_1(X1))) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(superposition,[],[f74,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f291,f212,f110,f186])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_23),
% 0.20/0.50    inference(resolution,[],[f213,f68])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl3_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f212])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    ~spl3_34 | spl3_16 | ~spl3_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f263,f247,f163,f278])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    spl3_16 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_16 | ~spl3_28)),
% 0.20/0.50    inference(superposition,[],[f164,f248])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f163])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    spl3_33 | ~spl3_15 | ~spl3_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f262,f247,f157,f274])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_15 | ~spl3_28)),
% 0.20/0.50    inference(superposition,[],[f158,f248])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f157])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    spl3_28 | ~spl3_12 | ~spl3_27),
% 0.20/0.50    inference(avatar_split_clause,[],[f256,f242,f136,f247])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    spl3_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    spl3_27 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_12 | ~spl3_27)),
% 0.20/0.50    inference(superposition,[],[f137,f243])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f242])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f136])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    spl3_27 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f240,f132,f128,f102,f242])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f239,f133])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_4 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f237,f129])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_4),
% 0.20/0.50    inference(resolution,[],[f81,f103])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f231,f209,f110,f186])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_22),
% 0.20/0.50    inference(resolution,[],[f210,f67])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    ~v1_relat_1(k2_funct_1(sK2)) | spl3_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f209])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl3_21),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    $false | spl3_21),
% 0.20/0.50    inference(resolution,[],[f200,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    spl3_21 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ~spl3_21 | ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f197,f186,f132,f128,f102,f199])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f196,f133])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | spl3_19)),
% 0.20/0.50    inference(forward_demodulation,[],[f194,f129])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl3_4 | spl3_19)),
% 0.20/0.50    inference(resolution,[],[f193,f103])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_19),
% 0.20/0.50    inference(resolution,[],[f187,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl3_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f186])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_20 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f183,f94,f190,f110,f186])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f69,f95])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    spl3_8 | ~spl3_7 | ~spl3_16 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f142,f128,f163,f114,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl3_8 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_10),
% 0.20/0.50    inference(superposition,[],[f66,f129])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl3_15 | ~spl3_5 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f155,f132,f128,f106,f157])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f141,f133])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f107,f129])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f106])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl3_14 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f150,f132,f128,f102,f152])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f140,f133])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f103,f129])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    spl3_12 | ~spl3_3 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f148,f132,f128,f98,f136])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f139,f133])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f99,f129])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~spl3_13 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f143,f132,f128,f90,f145])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl3_1 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f138,f133])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f91,f129])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f90])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl3_11 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f126,f122,f132])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f64,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl3_10 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f125,f114,f128])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.20/0.51    inference(resolution,[],[f64,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    l1_struct_0(sK1) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl3_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f122])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  % (11033)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ~spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f55,f118])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~v2_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f56,f114])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    l1_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl3_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f110])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f106])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f102])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f60,f98])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f61,f94])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    v2_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f62,f90])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11026)------------------------------
% 0.20/0.51  % (11026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11026)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11026)Memory used [KB]: 11129
% 0.20/0.51  % (11026)Time elapsed: 0.030 s
% 0.20/0.51  % (11026)------------------------------
% 0.20/0.51  % (11026)------------------------------
% 0.20/0.51  % (11036)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (11021)Refutation not found, incomplete strategy% (11021)------------------------------
% 0.20/0.51  % (11021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11021)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11021)Memory used [KB]: 10746
% 0.20/0.51  % (11021)Time elapsed: 0.094 s
% 0.20/0.51  % (11021)------------------------------
% 0.20/0.51  % (11021)------------------------------
% 0.20/0.51  % (11038)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (11033)Refutation not found, incomplete strategy% (11033)------------------------------
% 0.20/0.51  % (11033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11033)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11033)Memory used [KB]: 1663
% 0.20/0.51  % (11033)Time elapsed: 0.095 s
% 0.20/0.51  % (11033)------------------------------
% 0.20/0.51  % (11033)------------------------------
% 0.20/0.51  % (11019)Success in time 0.15 s
%------------------------------------------------------------------------------
