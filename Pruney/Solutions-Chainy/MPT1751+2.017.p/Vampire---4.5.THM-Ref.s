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
% DateTime   : Thu Dec  3 13:18:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 471 expanded)
%              Number of leaves         :   46 ( 176 expanded)
%              Depth                    :   22
%              Number of atoms          :  856 (1903 expanded)
%              Number of equality atoms :   98 ( 224 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f104,f109,f114,f119,f124,f129,f134,f148,f160,f173,f190,f203,f215,f236,f300,f306,f352,f364,f385,f392,f426,f543,f556,f769,f781,f888,f897])).

fof(f897,plain,
    ( ~ spl5_10
    | ~ spl5_20
    | spl5_55 ),
    inference(avatar_contradiction_clause,[],[f896])).

fof(f896,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_20
    | spl5_55 ),
    inference(subsumption_resolution,[],[f895,f209])).

fof(f209,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f895,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_10
    | spl5_55 ),
    inference(trivial_inequality_removal,[],[f894])).

fof(f894,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl5_10
    | spl5_55 ),
    inference(superposition,[],[f887,f155])).

fof(f155,plain,
    ( ! [X0] :
        ( k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4)
        | ~ v1_relat_1(X0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f147,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f147,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_10
  <=> r1_tarski(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f887,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4)
    | spl5_55 ),
    inference(avatar_component_clause,[],[f885])).

fof(f885,plain,
    ( spl5_55
  <=> k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f888,plain,
    ( ~ spl5_55
    | spl5_42
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f880,f778,f553,f885])).

fof(f553,plain,
    ( spl5_42
  <=> k9_relat_1(sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f778,plain,
    ( spl5_51
  <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f880,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4)
    | spl5_42
    | ~ spl5_51 ),
    inference(superposition,[],[f555,f786])).

fof(f786,plain,
    ( ! [X3] : k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X3) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X3)
    | ~ spl5_51 ),
    inference(resolution,[],[f780,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f780,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f778])).

fof(f555,plain,
    ( k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f553])).

fof(f781,plain,
    ( spl5_51
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f775,f766,f778])).

fof(f766,plain,
    ( spl5_50
  <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f775,plain,
    ( m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl5_50 ),
    inference(resolution,[],[f768,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f768,plain,
    ( r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f766])).

fof(f769,plain,
    ( spl5_50
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f747,f423,f233,f208,f170,f91,f766])).

% (7923)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f91,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f170,plain,
    ( spl5_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f233,plain,
    ( spl5_22
  <=> u1_struct_0(sK1) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f423,plain,
    ( spl5_37
  <=> u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f747,plain,
    ( r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(superposition,[],[f734,f425])).

fof(f425,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f423])).

fof(f734,plain,
    ( ! [X14] : r1_tarski(k7_relat_1(sK3,X14),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X14)),u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f705,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f705,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f703,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f703,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0))))
        | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f567,f398])).

fof(f398,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f329,f386])).

fof(f386,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f265,f235])).

fof(f235,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f233])).

fof(f265,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f137,f172])).

fof(f172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f137,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_partfun1(X6,X7,sK3,X8) = k7_relat_1(sK3,X8) )
    | ~ spl5_1 ),
    inference(resolution,[],[f93,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f93,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f329,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f328,f235])).

fof(f328,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f136,f172])).

fof(f136,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | m1_subset_1(k2_partfun1(X3,X4,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f93,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f567,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0))))
        | ~ v1_relat_1(X1) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f551,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f551,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0)))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f529,f217])).

fof(f217,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f216,f72])).

fof(f216,plain,
    ( ! [X1] : m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f175,f174])).

fof(f174,plain,
    ( ! [X0] : k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f81])).

fof(f175,plain,
    ( ! [X1] : m1_subset_1(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f529,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK3,X0),X1)
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f528,f209])).

% (7918)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (7925)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (7926)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK3,X0),X1)
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(superposition,[],[f525,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f525,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15)
        | m1_subset_1(k7_relat_1(sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X14)),X15)))
        | ~ v1_relat_1(k7_relat_1(sK3,X14)) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f524,f386])).

fof(f524,plain,
    ( ! [X14,X15] :
        ( m1_subset_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14)),X15)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15)
        | ~ v1_relat_1(k7_relat_1(sK3,X14)) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f523,f235])).

fof(f523,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15)
        | ~ v1_relat_1(k7_relat_1(sK3,X14))
        | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f522,f386])).

fof(f522,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(k2_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14)),X15)
        | ~ v1_relat_1(k7_relat_1(sK3,X14))
        | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f521,f235])).

fof(f521,plain,
    ( ! [X14,X15] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X14))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f520,f386])).

fof(f520,plain,
    ( ! [X14,X15] :
        ( ~ v1_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15))) )
    | ~ spl5_1
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f226,f235])).

fof(f226,plain,
    ( ! [X14,X15] :
        ( ~ v1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15))) )
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f218,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f218,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0))
    | ~ spl5_1
    | ~ spl5_14 ),
    inference(resolution,[],[f135,f172])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,sK3,X2)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f93,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f556,plain,
    ( ~ spl5_42
    | ~ spl5_14
    | spl5_16
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f545,f540,f187,f170,f553])).

fof(f187,plain,
    ( spl5_16
  <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f540,plain,
    ( spl5_40
  <=> k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f545,plain,
    ( k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ spl5_14
    | spl5_16
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f544,f174])).

fof(f544,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl5_16
    | ~ spl5_40 ),
    inference(superposition,[],[f189,f542])).

fof(f542,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f540])).

fof(f189,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f543,plain,
    ( spl5_40
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_14
    | ~ spl5_22
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f507,f361,f349,f233,f170,f131,f126,f121,f116,f111,f106,f101,f91,f540])).

fof(f101,plain,
    ( spl5_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f106,plain,
    ( spl5_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f111,plain,
    ( spl5_5
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f116,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f121,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f126,plain,
    ( spl5_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f131,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f349,plain,
    ( spl5_31
  <=> v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f361,plain,
    ( spl5_33
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f507,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_14
    | ~ spl5_22
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f506,f386])).

fof(f506,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_22
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f505,f93])).

fof(f505,plain,
    ( ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_22
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f503,f351])).

fof(f351,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f349])).

fof(f503,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3)
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_22
    | ~ spl5_33 ),
    inference(resolution,[],[f421,f363])).

fof(f363,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f361])).

fof(f421,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f420,f128])).

fof(f128,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f420,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f414,f118])).

fof(f118,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f414,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_1(X1)
        | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(resolution,[],[f344,f123])).

fof(f123,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f344,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X1))))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(X1),X0,u1_struct_0(sK2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(resolution,[],[f333,f133])).

fof(f133,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f333,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f332,f235])).

fof(f332,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_pre_topc(X2,sK1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f331,f235])).

fof(f331,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ m1_pre_topc(X2,sK1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f330,f235])).

fof(f330,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ m1_pre_topc(X2,sK1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f141,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ m1_pre_topc(X2,sK1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f140,f103])).

fof(f103,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ m1_pre_topc(X2,sK1)
        | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f108,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f108,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f426,plain,
    ( spl5_37
    | ~ spl5_20
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f397,f389,f208,f423])).

fof(f389,plain,
    ( spl5_36
  <=> r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f397,plain,
    ( u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl5_20
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f394,f209])).

fof(f394,plain,
    ( ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))
    | ~ spl5_36 ),
    inference(resolution,[],[f391,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f391,plain,
    ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f389])).

fof(f392,plain,
    ( spl5_36
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f387,f382,f389])).

fof(f382,plain,
    ( spl5_35
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f387,plain,
    ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3))
    | ~ spl5_35 ),
    inference(resolution,[],[f384,f72])).

fof(f384,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f382])).

fof(f385,plain,
    ( spl5_35
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f380,f233,f131,f111,f382])).

fof(f380,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3)))
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_22 ),
    inference(resolution,[],[f321,f133])).

fof(f321,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK1)
        | m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(k1_relat_1(sK3))) )
    | ~ spl5_5
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f318,f113])).

fof(f318,plain,
    ( ! [X3] :
        ( m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(k1_relat_1(sK3)))
        | ~ m1_pre_topc(X3,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl5_22 ),
    inference(superposition,[],[f61,f235])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f364,plain,
    ( spl5_33
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f312,f233,f170,f361])).

fof(f312,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | ~ spl5_14
    | ~ spl5_22 ),
    inference(superposition,[],[f172,f235])).

fof(f352,plain,
    ( spl5_31
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f309,f233,f157,f349])).

fof(f157,plain,
    ( spl5_12
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f309,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl5_12
    | ~ spl5_22 ),
    inference(superposition,[],[f159,f235])).

fof(f159,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f306,plain,
    ( ~ spl5_8
    | spl5_28 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl5_8
    | spl5_28 ),
    inference(subsumption_resolution,[],[f304,f128])).

fof(f304,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_28 ),
    inference(resolution,[],[f299,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f299,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl5_28
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f300,plain,
    ( ~ spl5_28
    | spl5_6
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f294,f229,f116,f297])).

fof(f229,plain,
    ( spl5_21
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f294,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f293,f118])).

fof(f293,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f290,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f290,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_21 ),
    inference(superposition,[],[f64,f231])).

fof(f231,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f236,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f227,f200,f170,f157,f233,f229])).

fof(f200,plain,
    ( spl5_18
  <=> k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f227,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f180,f202])).

fof(f202,plain,
    ( k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f180,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f177,f159])).

fof(f177,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f215,plain,
    ( ~ spl5_14
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl5_14
    | spl5_20 ),
    inference(subsumption_resolution,[],[f213,f66])).

fof(f213,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl5_14
    | spl5_20 ),
    inference(resolution,[],[f212,f172])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_20 ),
    inference(resolution,[],[f210,f62])).

fof(f210,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f203,plain,
    ( spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f178,f170,f200])).

fof(f178,plain,
    ( k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3)
    | ~ spl5_14 ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f190,plain,(
    ~ spl5_16 ),
    inference(avatar_split_clause,[],[f47,f187])).

fof(f47,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(X4,u1_struct_0(X2))
                         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

fof(f173,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f50,f170])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f160,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f49,f157])).

fof(f49,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f148,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f46,f145])).

fof(f46,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f134,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f52,f131])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f58,f126])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f57,f121])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f114,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f55,f111])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f106])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:01 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.22/0.48  % (7927)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (7921)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (7913)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (7916)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (7930)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (7929)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (7910)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7917)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (7914)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (7928)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (7911)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (7909)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (7922)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (7931)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (7931)Refutation not found, incomplete strategy% (7931)------------------------------
% 0.22/0.52  % (7931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7931)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7931)Memory used [KB]: 10618
% 0.22/0.52  % (7931)Time elapsed: 0.102 s
% 0.22/0.52  % (7931)------------------------------
% 0.22/0.52  % (7931)------------------------------
% 0.22/0.52  % (7913)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (7920)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (7924)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (7919)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f898,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f94,f104,f109,f114,f119,f124,f129,f134,f148,f160,f173,f190,f203,f215,f236,f300,f306,f352,f364,f385,f392,f426,f543,f556,f769,f781,f888,f897])).
% 0.22/0.52  fof(f897,plain,(
% 0.22/0.52    ~spl5_10 | ~spl5_20 | spl5_55),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f896])).
% 0.22/0.52  fof(f896,plain,(
% 0.22/0.52    $false | (~spl5_10 | ~spl5_20 | spl5_55)),
% 0.22/0.52    inference(subsumption_resolution,[],[f895,f209])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    v1_relat_1(sK3) | ~spl5_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f208])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    spl5_20 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.52  fof(f895,plain,(
% 0.22/0.52    ~v1_relat_1(sK3) | (~spl5_10 | spl5_55)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f894])).
% 0.22/0.52  fof(f894,plain,(
% 0.22/0.52    k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) | ~v1_relat_1(sK3) | (~spl5_10 | spl5_55)),
% 0.22/0.52    inference(superposition,[],[f887,f155])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X0] : (k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4) | ~v1_relat_1(X0)) ) | ~spl5_10),
% 0.22/0.52    inference(resolution,[],[f147,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    r1_tarski(sK4,u1_struct_0(sK2)) | ~spl5_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f145])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    spl5_10 <=> r1_tarski(sK4,u1_struct_0(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.52  fof(f887,plain,(
% 0.22/0.52    k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) | spl5_55),
% 0.22/0.52    inference(avatar_component_clause,[],[f885])).
% 0.22/0.52  fof(f885,plain,(
% 0.22/0.52    spl5_55 <=> k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 0.22/0.52  fof(f888,plain,(
% 0.22/0.52    ~spl5_55 | spl5_42 | ~spl5_51),
% 0.22/0.52    inference(avatar_split_clause,[],[f880,f778,f553,f885])).
% 0.22/0.52  fof(f553,plain,(
% 0.22/0.52    spl5_42 <=> k9_relat_1(sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.22/0.52  fof(f778,plain,(
% 0.22/0.52    spl5_51 <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.22/0.52  fof(f880,plain,(
% 0.22/0.52    k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) | (spl5_42 | ~spl5_51)),
% 0.22/0.52    inference(superposition,[],[f555,f786])).
% 0.22/0.52  fof(f786,plain,(
% 0.22/0.52    ( ! [X3] : (k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X3) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X3)) ) | ~spl5_51),
% 0.22/0.52    inference(resolution,[],[f780,f81])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f780,plain,(
% 0.22/0.52    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl5_51),
% 0.22/0.52    inference(avatar_component_clause,[],[f778])).
% 0.22/0.52  fof(f555,plain,(
% 0.22/0.52    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | spl5_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f553])).
% 0.22/0.52  fof(f781,plain,(
% 0.22/0.52    spl5_51 | ~spl5_50),
% 0.22/0.52    inference(avatar_split_clause,[],[f775,f766,f778])).
% 0.22/0.52  fof(f766,plain,(
% 0.22/0.52    spl5_50 <=> r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.22/0.52  fof(f775,plain,(
% 0.22/0.52    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl5_50),
% 0.22/0.52    inference(resolution,[],[f768,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f768,plain,(
% 0.22/0.52    r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | ~spl5_50),
% 0.22/0.52    inference(avatar_component_clause,[],[f766])).
% 0.22/0.52  fof(f769,plain,(
% 0.22/0.52    spl5_50 | ~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22 | ~spl5_37),
% 0.22/0.52    inference(avatar_split_clause,[],[f747,f423,f233,f208,f170,f91,f766])).
% 0.22/0.52  % (7923)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl5_1 <=> v1_funct_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    spl5_14 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    spl5_22 <=> u1_struct_0(sK1) = k1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.52  fof(f423,plain,(
% 0.22/0.52    spl5_37 <=> u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.52  fof(f747,plain,(
% 0.22/0.52    r1_tarski(k7_relat_1(sK3,u1_struct_0(sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22 | ~spl5_37)),
% 0.22/0.52    inference(superposition,[],[f734,f425])).
% 0.22/0.52  fof(f425,plain,(
% 0.22/0.52    u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~spl5_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f423])).
% 0.22/0.52  fof(f734,plain,(
% 0.22/0.52    ( ! [X14] : (r1_tarski(k7_relat_1(sK3,X14),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X14)),u1_struct_0(sK0)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.52    inference(resolution,[],[f705,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f705,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.52    inference(subsumption_resolution,[],[f703,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f703,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0)))) | ~v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.53    inference(resolution,[],[f567,f398])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f329,f386])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f265,f235])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    u1_struct_0(sK1) = k1_relat_1(sK3) | ~spl5_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f233])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl5_1 | ~spl5_14)),
% 0.22/0.53    inference(resolution,[],[f137,f172])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X6,X8,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_partfun1(X6,X7,sK3,X8) = k7_relat_1(sK3,X8)) ) | ~spl5_1),
% 0.22/0.53    inference(resolution,[],[f93,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    v1_funct_1(sK3) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.53    inference(forward_demodulation,[],[f328,f235])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_14)),
% 0.22/0.53    inference(resolution,[],[f136,f172])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k2_partfun1(X3,X4,sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl5_1),
% 0.22/0.53    inference(resolution,[],[f93,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.22/0.53  fof(f567,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(X1)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0)))) | ~v1_relat_1(X1)) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.53    inference(resolution,[],[f551,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f551,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0))))) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.53    inference(resolution,[],[f529,f217])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0))) ) | ~spl5_14),
% 0.22/0.53    inference(resolution,[],[f216,f72])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_14),
% 0.22/0.53    inference(forward_demodulation,[],[f175,f174])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl5_14),
% 0.22/0.53    inference(resolution,[],[f172,f81])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X1] : (m1_subset_1(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_14),
% 0.22/0.53    inference(resolution,[],[f172,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.53  fof(f529,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK3,X0),X1) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl5_1 | ~spl5_14 | ~spl5_20 | ~spl5_22)),
% 0.22/0.53    inference(subsumption_resolution,[],[f528,f209])).
% 0.22/0.53  % (7918)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (7925)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (7926)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  fof(f528,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK3,X0),X1) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),X1))) | ~v1_relat_1(k7_relat_1(sK3,X0)) | ~v1_relat_1(sK3)) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(superposition,[],[f525,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.54  fof(f525,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15) | m1_subset_1(k7_relat_1(sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X14)),X15))) | ~v1_relat_1(k7_relat_1(sK3,X14))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f524,f386])).
% 0.22/0.54  fof(f524,plain,(
% 0.22/0.54    ( ! [X14,X15] : (m1_subset_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14)),X15))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15) | ~v1_relat_1(k7_relat_1(sK3,X14))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f523,f235])).
% 0.22/0.54  fof(f523,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,X14)),X15) | ~v1_relat_1(k7_relat_1(sK3,X14)) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f522,f386])).
% 0.22/0.54  fof(f522,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~r1_tarski(k2_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14)),X15) | ~v1_relat_1(k7_relat_1(sK3,X14)) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f521,f235])).
% 0.22/0.54  fof(f521,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~v1_relat_1(k7_relat_1(sK3,X14)) | ~r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f520,f386])).
% 0.22/0.54  fof(f520,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~v1_relat_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X14)) | ~r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)))) ) | (~spl5_1 | ~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f226,f235])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ( ! [X14,X15] : (~v1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)) | ~r1_tarski(k2_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X14)),X15)))) ) | (~spl5_1 | ~spl5_14)),
% 0.22/0.54    inference(resolution,[],[f218,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ( ! [X0] : (v1_funct_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0))) ) | (~spl5_1 | ~spl5_14)),
% 0.22/0.54    inference(resolution,[],[f135,f172])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))) ) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f93,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f556,plain,(
% 0.22/0.54    ~spl5_42 | ~spl5_14 | spl5_16 | ~spl5_40),
% 0.22/0.54    inference(avatar_split_clause,[],[f545,f540,f187,f170,f553])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    spl5_16 <=> k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) = k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.54  fof(f540,plain,(
% 0.22/0.54    spl5_40 <=> k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.22/0.54  fof(f545,plain,(
% 0.22/0.54    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (~spl5_14 | spl5_16 | ~spl5_40)),
% 0.22/0.54    inference(forward_demodulation,[],[f544,f174])).
% 0.22/0.54  fof(f544,plain,(
% 0.22/0.54    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (spl5_16 | ~spl5_40)),
% 0.22/0.54    inference(superposition,[],[f189,f542])).
% 0.22/0.54  fof(f542,plain,(
% 0.22/0.54    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | ~spl5_40),
% 0.22/0.54    inference(avatar_component_clause,[],[f540])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) | spl5_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f187])).
% 0.22/0.54  fof(f543,plain,(
% 0.22/0.54    spl5_40 | ~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_14 | ~spl5_22 | ~spl5_31 | ~spl5_33),
% 0.22/0.54    inference(avatar_split_clause,[],[f507,f361,f349,f233,f170,f131,f126,f121,f116,f111,f106,f101,f91,f540])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl5_3 <=> v2_struct_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl5_4 <=> v2_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    spl5_5 <=> l1_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl5_6 <=> v2_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl5_7 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    spl5_8 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    spl5_9 <=> m1_pre_topc(sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    spl5_31 <=> v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    spl5_33 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.54  fof(f507,plain,(
% 0.22/0.54    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_14 | ~spl5_22 | ~spl5_31 | ~spl5_33)),
% 0.22/0.54    inference(forward_demodulation,[],[f506,f386])).
% 0.22/0.54  fof(f506,plain,(
% 0.22/0.54    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_22 | ~spl5_31 | ~spl5_33)),
% 0.22/0.54    inference(subsumption_resolution,[],[f505,f93])).
% 0.22/0.54  fof(f505,plain,(
% 0.22/0.54    ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | (spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_22 | ~spl5_31 | ~spl5_33)),
% 0.22/0.54    inference(subsumption_resolution,[],[f503,f351])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | ~spl5_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f349])).
% 0.22/0.54  fof(f503,plain,(
% 0.22/0.54    ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK3) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) | (spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_22 | ~spl5_33)),
% 0.22/0.54    inference(resolution,[],[f421,f363])).
% 0.22/0.54  fof(f363,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~spl5_33),
% 0.22/0.54    inference(avatar_component_clause,[],[f361])).
% 0.22/0.54  fof(f421,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(X1) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f420,f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f126])).
% 0.22/0.54  fof(f420,plain,(
% 0.22/0.54    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f414,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    ~v2_struct_0(sK0) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f116])).
% 0.22/0.54  fof(f414,plain,(
% 0.22/0.54    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | k2_tmap_1(sK1,sK0,X1,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X1,u1_struct_0(sK2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_9 | ~spl5_22)),
% 0.22/0.54    inference(resolution,[],[f344,f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f121])).
% 0.22/0.54  fof(f344,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | k2_tmap_1(sK1,X1,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(X1),X0,u1_struct_0(sK2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_22)),
% 0.22/0.54    inference(resolution,[],[f333,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK1) | ~spl5_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f131])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f332,f235])).
% 0.22/0.54  fof(f332,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_pre_topc(X2,sK1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f331,f235])).
% 0.22/0.54  fof(f331,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X1,k1_relat_1(sK3),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_pre_topc(X2,sK1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_22)),
% 0.22/0.54    inference(forward_demodulation,[],[f330,f235])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_pre_topc(X2,sK1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f113])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    l1_pre_topc(sK1) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f111])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_pre_topc(X2,sK1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | (spl5_3 | ~spl5_4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f140,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ~v2_struct_0(sK1) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f101])).
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_pre_topc(X2,sK1) | k2_tmap_1(sK1,X0,X1,X2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),X1,u1_struct_0(X2))) ) | ~spl5_4),
% 0.22/0.54    inference(resolution,[],[f108,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    v2_pre_topc(sK1) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f106])).
% 0.22/0.54  fof(f426,plain,(
% 0.22/0.54    spl5_37 | ~spl5_20 | ~spl5_36),
% 0.22/0.54    inference(avatar_split_clause,[],[f397,f389,f208,f423])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    spl5_36 <=> r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | (~spl5_20 | ~spl5_36)),
% 0.22/0.54    inference(subsumption_resolution,[],[f394,f209])).
% 0.22/0.54  fof(f394,plain,(
% 0.22/0.54    ~v1_relat_1(sK3) | u1_struct_0(sK2) = k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) | ~spl5_36),
% 0.22/0.54    inference(resolution,[],[f391,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.54  fof(f391,plain,(
% 0.22/0.54    r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) | ~spl5_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f389])).
% 0.22/0.54  fof(f392,plain,(
% 0.22/0.54    spl5_36 | ~spl5_35),
% 0.22/0.54    inference(avatar_split_clause,[],[f387,f382,f389])).
% 0.22/0.54  fof(f382,plain,(
% 0.22/0.54    spl5_35 <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.54  fof(f387,plain,(
% 0.22/0.54    r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) | ~spl5_35),
% 0.22/0.54    inference(resolution,[],[f384,f72])).
% 0.22/0.54  fof(f384,plain,(
% 0.22/0.54    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3))) | ~spl5_35),
% 0.22/0.54    inference(avatar_component_clause,[],[f382])).
% 0.22/0.54  fof(f385,plain,(
% 0.22/0.54    spl5_35 | ~spl5_5 | ~spl5_9 | ~spl5_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f380,f233,f131,f111,f382])).
% 0.22/0.54  fof(f380,plain,(
% 0.22/0.54    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k1_relat_1(sK3))) | (~spl5_5 | ~spl5_9 | ~spl5_22)),
% 0.22/0.54    inference(resolution,[],[f321,f133])).
% 0.22/0.54  fof(f321,plain,(
% 0.22/0.54    ( ! [X3] : (~m1_pre_topc(X3,sK1) | m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(k1_relat_1(sK3)))) ) | (~spl5_5 | ~spl5_22)),
% 0.22/0.54    inference(subsumption_resolution,[],[f318,f113])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    ( ! [X3] : (m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(k1_relat_1(sK3))) | ~m1_pre_topc(X3,sK1) | ~l1_pre_topc(sK1)) ) | ~spl5_22),
% 0.22/0.54    inference(superposition,[],[f61,f235])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.54  fof(f364,plain,(
% 0.22/0.54    spl5_33 | ~spl5_14 | ~spl5_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f312,f233,f170,f361])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | (~spl5_14 | ~spl5_22)),
% 0.22/0.54    inference(superposition,[],[f172,f235])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    spl5_31 | ~spl5_12 | ~spl5_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f309,f233,f157,f349])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    spl5_12 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | (~spl5_12 | ~spl5_22)),
% 0.22/0.54    inference(superposition,[],[f159,f235])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl5_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f157])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    ~spl5_8 | spl5_28),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f305])).
% 0.22/0.54  fof(f305,plain,(
% 0.22/0.54    $false | (~spl5_8 | spl5_28)),
% 0.22/0.54    inference(subsumption_resolution,[],[f304,f128])).
% 0.22/0.54  fof(f304,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | spl5_28),
% 0.22/0.54    inference(resolution,[],[f299,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    ~l1_struct_0(sK0) | spl5_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f297])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    spl5_28 <=> l1_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~spl5_28 | spl5_6 | ~spl5_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f294,f229,f116,f297])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    spl5_21 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    ~l1_struct_0(sK0) | (spl5_6 | ~spl5_21)),
% 0.22/0.54    inference(subsumption_resolution,[],[f293,f118])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_21),
% 0.22/0.54    inference(subsumption_resolution,[],[f290,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_21),
% 0.22/0.54    inference(superposition,[],[f64,f231])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK0) | ~spl5_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f229])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    spl5_21 | spl5_22 | ~spl5_12 | ~spl5_14 | ~spl5_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f227,f200,f170,f157,f233,f229])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl5_18 <=> k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    u1_struct_0(sK1) = k1_relat_1(sK3) | k1_xboole_0 = u1_struct_0(sK0) | (~spl5_12 | ~spl5_14 | ~spl5_18)),
% 0.22/0.54    inference(forward_demodulation,[],[f180,f202])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) | ~spl5_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f200])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) | (~spl5_12 | ~spl5_14)),
% 0.22/0.54    inference(subsumption_resolution,[],[f177,f159])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    k1_xboole_0 = u1_struct_0(sK0) | u1_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f172,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    ~spl5_14 | spl5_20),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f214])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    $false | (~spl5_14 | spl5_20)),
% 0.22/0.54    inference(subsumption_resolution,[],[f213,f66])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) | (~spl5_14 | spl5_20)),
% 0.22/0.54    inference(resolution,[],[f212,f172])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_20),
% 0.22/0.54    inference(resolution,[],[f210,f62])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    ~v1_relat_1(sK3) | spl5_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f208])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    spl5_18 | ~spl5_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f178,f170,f200])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    k1_relat_1(sK3) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) | ~spl5_14),
% 0.22/0.54    inference(resolution,[],[f172,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f190,plain,(
% 0.22/0.54    ~spl5_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f187])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f19])).
% 0.22/0.54  fof(f19,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    spl5_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f50,f170])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    spl5_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f157])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    spl5_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f145])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    r1_tarski(sK4,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl5_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f131])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    spl5_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f58,f126])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl5_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f57,f121])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f56,f116])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f111])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f54,f106])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    v2_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f101])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f91])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (7913)------------------------------
% 0.22/0.54  % (7913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7913)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (7913)Memory used [KB]: 11385
% 0.22/0.54  % (7913)Time elapsed: 0.099 s
% 0.22/0.54  % (7913)------------------------------
% 0.22/0.54  % (7913)------------------------------
% 0.22/0.54  % (7905)Success in time 0.18 s
%------------------------------------------------------------------------------
