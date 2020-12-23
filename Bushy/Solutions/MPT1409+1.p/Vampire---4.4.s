%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t3_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:09 EDT 2019

% Result     : Theorem 8.63s
% Output     : Refutation 8.63s
% Verified   : 
% Statistics : Number of formulae       :  341 ( 742 expanded)
%              Number of leaves         :   89 ( 349 expanded)
%              Depth                    :   14
%              Number of atoms          : 1622 (3343 expanded)
%              Number of equality atoms :  107 ( 277 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f177,f181,f185,f189,f193,f197,f201,f205,f209,f237,f246,f747,f840,f856,f898,f1100,f1200,f1234,f1346,f1373,f1419,f1488,f1498,f1512,f1528,f1559,f2336,f2352,f2500,f2580,f4964,f6039,f6044,f6131,f7171,f7176,f7740,f7746,f7773,f7777,f7784,f7788,f7821,f7826,f16397,f39259,f39269,f41768,f41890,f42464,f42579])).

fof(f42579,plain,
    ( spl14_540
    | spl14_16
    | spl14_5050
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f35714,f175,f35720,f275,f2495])).

fof(f2495,plain,
    ( spl14_540
  <=> ! [X1,X0] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_540])])).

fof(f275,plain,
    ( spl14_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f35720,plain,
    ( spl14_5050
  <=> ! [X1,X5,X7,X0,X2,X6] :
        ( k1_binop_1(sK4,X0,X1) = k4_binop_1(X2,sK4,X0,X1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ m2_filter_1(sK4,X2,X5)
        | ~ m1_subset_1(X1,X2)
        | ~ m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5050])])).

fof(f175,plain,
    ( spl14_2
  <=> m2_filter_1(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f35714,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( k1_binop_1(sK4,X0,X1) = k4_binop_1(X2,sK4,X0,X1)
        | ~ m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,X2)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ m2_filter_1(sK4,X2,X5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl14_2 ),
    inference(resolution,[],[f13184,f176])).

fof(f176,plain,
    ( m2_filter_1(sK4,sK0,sK1)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f175])).

fof(f13184,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( ~ m2_filter_1(X2,X4,X5)
      | k1_binop_1(X2,X0,X3) = k4_binop_1(X1,X2,X0,X3)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m2_filter_1(X2,X1,X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f5684,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc1_relset_1)).

fof(f5684,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X2,X1)
      | k1_binop_1(X0,X2,X3) = k4_binop_1(X1,X0,X2,X3)
      | ~ m2_filter_1(X0,X4,X5)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m2_filter_1(X0,X1,X8)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f2826,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_m2_filter_1)).

fof(f2826,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_2(X2,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ m1_subset_1(X0,X1)
      | k1_binop_1(X2,X0,X3) = k4_binop_1(X1,X2,X0,X3)
      | ~ m2_filter_1(X2,X4,X5)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f1606,f156])).

fof(f1606,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | k1_binop_1(X3,X2,X0) = k4_binop_1(X1,X3,X2,X0)
      | ~ m2_filter_1(X3,X4,X5)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f167,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k1_binop_1(X1,X2,X3) = k4_binop_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k4_binop_1)).

fof(f42464,plain,
    ( ~ spl14_2
    | ~ spl14_8
    | ~ spl14_5348 ),
    inference(avatar_contradiction_clause,[],[f42463])).

fof(f42463,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_5348 ),
    inference(subsumption_resolution,[],[f188,f38848])).

fof(f38848,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl14_2
    | ~ spl14_5348 ),
    inference(resolution,[],[f38831,f176])).

fof(f38831,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_filter_1(sK4,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl14_5348 ),
    inference(avatar_component_clause,[],[f38830])).

fof(f38830,plain,
    ( spl14_5348
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m2_filter_1(sK4,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5348])])).

fof(f188,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl14_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f41890,plain,
    ( spl14_96
    | spl14_158
    | ~ spl14_301
    | spl14_514
    | ~ spl14_504 ),
    inference(avatar_split_clause,[],[f2404,f2350,f2381,f1681,f865,f479])).

fof(f479,plain,
    ( spl14_96
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f865,plain,
    ( spl14_158
  <=> v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_158])])).

fof(f1681,plain,
    ( spl14_301
  <=> ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_301])])).

fof(f2381,plain,
    ( spl14_514
  <=> ! [X0] :
        ( m1_subset_1(k11_relat_1(sK1,X0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_514])])).

fof(f2350,plain,
    ( spl14_504
  <=> ! [X0] :
        ( m2_subset_1(k11_relat_1(sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_504])])).

fof(f2404,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k11_relat_1(sK1,X0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl14_504 ),
    inference(resolution,[],[f2351,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_m2_subset_1)).

fof(f2351,plain,
    ( ! [X0] :
        ( m2_subset_1(k11_relat_1(sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_504 ),
    inference(avatar_component_clause,[],[f2350])).

fof(f41768,plain,(
    ~ spl14_24 ),
    inference(avatar_contradiction_clause,[],[f41739])).

fof(f41739,plain,
    ( $false
    | ~ spl14_24 ),
    inference(resolution,[],[f233,f137])).

fof(f137,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f27,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',existence_m1_subset_1)).

fof(f233,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl14_24
  <=> ! [X0] : ~ m1_subset_1(X0,sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f39269,plain,
    ( ~ spl14_5
    | ~ spl14_7
    | spl14_1643
    | ~ spl14_5368 ),
    inference(avatar_split_clause,[],[f39266,f39257,f16395,f16389,f16392])).

fof(f16392,plain,
    ( spl14_5
  <=> ~ m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f16389,plain,
    ( spl14_7
  <=> ~ m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f16395,plain,
    ( spl14_1643
  <=> k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1643])])).

fof(f39257,plain,
    ( spl14_5368
  <=> ! [X3,X4] :
        ( k1_binop_1(sK4,X3,X4) = k4_binop_1(sK0,sK4,X3,X4)
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5368])])).

fof(f39266,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl14_1643
    | ~ spl14_5368 ),
    inference(trivial_inequality_removal,[],[f39261])).

fof(f39261,plain,
    ( k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3)) != k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl14_1643
    | ~ spl14_5368 ),
    inference(superposition,[],[f16396,f39258])).

fof(f39258,plain,
    ( ! [X4,X3] :
        ( k1_binop_1(sK4,X3,X4) = k4_binop_1(sK0,sK4,X3,X4)
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X4,sK0) )
    | ~ spl14_5368 ),
    inference(avatar_component_clause,[],[f39257])).

fof(f16396,plain,
    ( k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
    | ~ spl14_1643 ),
    inference(avatar_component_clause,[],[f16395])).

fof(f39259,plain,
    ( spl14_5368
    | spl14_16
    | spl14_5348
    | ~ spl14_542
    | ~ spl14_5050 ),
    inference(avatar_split_clause,[],[f39255,f35720,f2498,f38830,f275,f39257])).

fof(f2498,plain,
    ( spl14_542
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_542])])).

fof(f39255,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(sK0)
        | k1_binop_1(sK4,X3,X4) = k4_binop_1(sK0,sK4,X3,X4)
        | ~ m2_filter_1(sK4,sK0,X0)
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X3,sK0) )
    | ~ spl14_542
    | ~ spl14_5050 ),
    inference(resolution,[],[f35721,f2499])).

fof(f2499,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl14_542 ),
    inference(avatar_component_clause,[],[f2498])).

fof(f35721,plain,
    ( ! [X6,X2,X0,X7,X5,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | v1_xboole_0(X2)
        | k1_binop_1(sK4,X0,X1) = k4_binop_1(X2,sK4,X0,X1)
        | ~ m2_filter_1(sK4,X2,X5)
        | ~ m1_subset_1(X1,X2)
        | ~ m1_subset_1(X0,X2) )
    | ~ spl14_5050 ),
    inference(avatar_component_clause,[],[f35720])).

fof(f16397,plain,
    ( ~ spl14_7
    | ~ spl14_5
    | ~ spl14_1643
    | spl14_137
    | ~ spl14_514
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(avatar_split_clause,[],[f16387,f7824,f6042,f2381,f742,f16395,f16392,f16389])).

fof(f742,plain,
    ( spl14_137
  <=> k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_137])])).

fof(f6042,plain,
    ( spl14_906
  <=> ! [X0] :
        ( r2_hidden(X0,k11_relat_1(sK1,X0))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_906])])).

fof(f7824,plain,
    ( spl14_1024
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X2,k8_eqrel_1(sK0,sK1))
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X2) = k11_relat_1(sK1,k1_binop_1(sK4,X3,X1))
        | ~ r2_hidden(X3,X0)
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1024])])).

fof(f16387,plain,
    ( k11_relat_1(sK1,k1_binop_1(sK4,sK2,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
    | ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl14_137
    | ~ spl14_514
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(superposition,[],[f743,f16380])).

fof(f16380,plain,
    ( ! [X0,X1] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,X0),k11_relat_1(sK1,X1)) = k11_relat_1(sK1,k1_binop_1(sK4,X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_514
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(duplicate_literal_removal,[],[f16376])).

fof(f16376,plain,
    ( ! [X0,X1] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,X0),k11_relat_1(sK1,X1)) = k11_relat_1(sK1,k1_binop_1(sK4,X0,X1))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl14_514
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(resolution,[],[f15973,f2382])).

fof(f2382,plain,
    ( ! [X0] :
        ( m1_subset_1(k11_relat_1(sK1,X0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_514 ),
    inference(avatar_component_clause,[],[f2381])).

fof(f15973,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k11_relat_1(sK1,X4),k8_eqrel_1(sK0,sK1))
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,X3),k11_relat_1(sK1,X4)) = k11_relat_1(sK1,k1_binop_1(sK4,X3,X4))
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X3,sK0) )
    | ~ spl14_514
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(subsumption_resolution,[],[f14390,f2382])).

fof(f14390,plain,
    ( ! [X4,X3] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,X3),k11_relat_1(sK1,X4)) = k11_relat_1(sK1,k1_binop_1(sK4,X3,X4))
        | ~ m1_subset_1(k11_relat_1(sK1,X4),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(k11_relat_1(sK1,X3),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X3,sK0) )
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(resolution,[],[f7828,f6043])).

fof(f6043,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k11_relat_1(sK1,X0))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_906 ),
    inference(avatar_component_clause,[],[f6042])).

fof(f7828,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X6,X5)
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X5,k11_relat_1(sK1,X4)) = k11_relat_1(sK1,k1_binop_1(sK4,X6,X4))
        | ~ m1_subset_1(k11_relat_1(sK1,X4),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X5,k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X4,sK0) )
    | ~ spl14_906
    | ~ spl14_1024 ),
    inference(resolution,[],[f7825,f6043])).

fof(f7825,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k8_eqrel_1(sK0,sK1))
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X2) = k11_relat_1(sK1,k1_binop_1(sK4,X3,X1))
        | ~ r2_hidden(X3,X0)
        | ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1)) )
    | ~ spl14_1024 ),
    inference(avatar_component_clause,[],[f7824])).

fof(f743,plain,
    ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
    | ~ spl14_137 ),
    inference(avatar_component_clause,[],[f742])).

fof(f7826,plain,
    ( spl14_158
    | spl14_1024
    | ~ spl14_1022 ),
    inference(avatar_split_clause,[],[f7822,f7819,f7824,f865])).

fof(f7819,plain,
    ( spl14_1022
  <=> ! [X1,X3,X0,X2] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X3))
        | ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1022])])).

fof(f7822,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X3,X0)
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X2) = k11_relat_1(sK1,k1_binop_1(sK4,X3,X1))
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X2,k8_eqrel_1(sK0,sK1)) )
    | ~ spl14_1022 ),
    inference(resolution,[],[f7820,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t2_subset)).

fof(f7820,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X2,X0)
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X3)) )
    | ~ spl14_1022 ),
    inference(avatar_component_clause,[],[f7819])).

fof(f7821,plain,
    ( spl14_158
    | spl14_1022
    | ~ spl14_1018 ),
    inference(avatar_split_clause,[],[f7817,f7771,f7819,f865])).

fof(f7771,plain,
    ( spl14_1018
  <=> ! [X1,X3,X0,X2] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),X3,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X0))
        | ~ r2_hidden(X3,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1018])])).

fof(f7817,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),X0,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X3))
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X3,X1)
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,k8_eqrel_1(sK0,sK1)) )
    | ~ spl14_1018 ),
    inference(resolution,[],[f7772,f141])).

fof(f7772,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X3,k8_eqrel_1(sK0,sK1))
        | k1_binop_1(k3_filter_1(sK0,sK1,sK4),X3,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X0))
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X0,X1) )
    | ~ spl14_1018 ),
    inference(avatar_component_clause,[],[f7771])).

fof(f7788,plain,
    ( ~ spl14_2
    | ~ spl14_8
    | ~ spl14_1020 ),
    inference(avatar_contradiction_clause,[],[f7787])).

fof(f7787,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_1020 ),
    inference(subsumption_resolution,[],[f188,f7786])).

fof(f7786,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl14_2
    | ~ spl14_1020 ),
    inference(resolution,[],[f7785,f176])).

fof(f7785,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_filter_1(sK4,sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl14_1020 ),
    inference(resolution,[],[f7783,f156])).

fof(f7783,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m2_filter_1(sK4,sK0,X0) )
    | ~ spl14_1020 ),
    inference(avatar_component_clause,[],[f7782])).

fof(f7782,plain,
    ( spl14_1020
  <=> ! [X0] :
        ( ~ m2_filter_1(sK4,sK0,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1020])])).

fof(f7784,plain,
    ( spl14_16
    | spl14_1020
    | spl14_1017 ),
    inference(avatar_split_clause,[],[f7780,f7765,f7782,f275])).

fof(f7765,plain,
    ( spl14_1017
  <=> ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1017])])).

fof(f7780,plain,
    ( ! [X0] :
        ( ~ m2_filter_1(sK4,sK0,X0)
        | ~ v1_relat_1(X0)
        | v1_xboole_0(sK0) )
    | ~ spl14_1017 ),
    inference(resolution,[],[f7766,f147])).

fof(f7766,plain,
    ( ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl14_1017 ),
    inference(avatar_component_clause,[],[f7765])).

fof(f7777,plain,
    ( spl14_540
    | spl14_16
    | ~ spl14_2
    | spl14_1015 ),
    inference(avatar_split_clause,[],[f7776,f7762,f175,f275,f2495])).

fof(f7762,plain,
    ( spl14_1015
  <=> ~ v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1015])])).

fof(f7776,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl14_2
    | ~ spl14_1015 ),
    inference(resolution,[],[f7775,f176])).

fof(f7775,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m2_filter_1(sK4,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl14_1015 ),
    inference(resolution,[],[f7774,f156])).

fof(f7774,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ m2_filter_1(sK4,X0,X1)
        | v1_xboole_0(X0) )
    | ~ spl14_1015 ),
    inference(resolution,[],[f7763,f146])).

fof(f7763,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl14_1015 ),
    inference(avatar_component_clause,[],[f7762])).

fof(f7773,plain,
    ( spl14_16
    | ~ spl14_15
    | ~ spl14_13
    | ~ spl14_11
    | ~ spl14_9
    | ~ spl14_1015
    | ~ spl14_1017
    | ~ spl14_3
    | spl14_1018
    | ~ spl14_8
    | ~ spl14_1010 ),
    inference(avatar_split_clause,[],[f7760,f7738,f187,f7771,f7768,f7765,f7762,f1229,f1226,f835,f851,f275])).

fof(f851,plain,
    ( spl14_15
  <=> ~ v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f835,plain,
    ( spl14_13
  <=> ~ v3_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f1226,plain,
    ( spl14_11
  <=> ~ v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f1229,plain,
    ( spl14_9
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f7768,plain,
    ( spl14_3
  <=> ~ m2_filter_1(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f7738,plain,
    ( spl14_1010
  <=> v1_funct_1(k3_filter_1(sK0,sK1,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1010])])).

fof(f7760,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),X3,X1) = k11_relat_1(sK1,k1_binop_1(sK4,X2,X0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X3,k8_eqrel_1(sK0,sK1))
        | ~ m2_filter_1(sK4,sK0,sK1)
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v8_relat_2(sK1)
        | ~ v3_relat_2(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl14_8
    | ~ spl14_1010 ),
    inference(forward_demodulation,[],[f7747,f711])).

fof(f711,plain,
    ( ! [X5] : k6_eqrel_1(sK0,sK0,sK1,X5) = k11_relat_1(sK1,X5)
    | ~ spl14_8 ),
    inference(resolution,[],[f165,f188])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_eqrel_1(X0,X1,X2,X3) = k11_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k6_eqrel_1)).

fof(f7747,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X1,k8_eqrel_1(sK0,sK1))
        | ~ r2_hidden(X3,k8_eqrel_1(sK0,sK1))
        | k6_eqrel_1(sK0,sK0,sK1,k1_binop_1(sK4,X2,X0)) = k1_binop_1(k3_filter_1(sK0,sK1,sK4),X3,X1)
        | ~ m2_filter_1(sK4,sK0,sK1)
        | ~ v1_funct_2(sK4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v8_relat_2(sK1)
        | ~ v3_relat_2(sK1)
        | ~ v1_partfun1(sK1,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl14_1010 ),
    inference(resolution,[],[f7739,f761])).

fof(f761,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f211,f760])).

fof(f760,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m2_filter_1(X0,X1,X2)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f148,f156])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m2_filter_1(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f211,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9)
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f210,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k3_filter_1)).

fof(f210,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9)
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | ~ v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f169,f161])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f169,plain,(
    ! [X2,X0,X10,X8,X1,X11,X9] :
      ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(k3_filter_1(X0,X1,X2),X8,X9)
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X10,X8,X3,X1,X11,X9] :
      ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(X3,X8,X9)
      | ~ r2_hidden(X11,X9)
      | ~ r2_hidden(X10,X8)
      | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
      | ~ r2_hidden(X8,k8_eqrel_1(X0,X1))
      | k3_filter_1(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ v1_funct_1(X3)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3))) != k1_binop_1(X3,sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
                        & r2_hidden(sK8(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
                        & r2_hidden(sK7(X0,X1,X2,X3),sK5(X0,X1,X2,X3))
                        & r2_hidden(sK6(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
                        & r2_hidden(sK5(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(X3,X8,X9)
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f102,f103])).

fof(f103,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6,X7] :
          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) != k1_binop_1(X3,X4,X5)
          & r2_hidden(X7,X5)
          & r2_hidden(X6,X4)
          & r2_hidden(X5,k8_eqrel_1(X0,X1))
          & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
     => ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,sK7(X0,X1,X2,X3),sK8(X0,X1,X2,X3))) != k1_binop_1(X3,sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
        & r2_hidden(sK8(X0,X1,X2,X3),sK6(X0,X1,X2,X3))
        & r2_hidden(sK7(X0,X1,X2,X3),sK5(X0,X1,X2,X3))
        & r2_hidden(sK6(X0,X1,X2,X3),k8_eqrel_1(X0,X1))
        & r2_hidden(sK5(X0,X1,X2,X3),k8_eqrel_1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) != k1_binop_1(X3,X4,X5)
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X8,X9,X10,X11] :
                          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X10,X11)) = k1_binop_1(X3,X8,X9)
                          | ~ r2_hidden(X11,X9)
                          | ~ r2_hidden(X10,X8)
                          | ~ r2_hidden(X9,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X8,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_filter_1(X0,X1,X2) = X3
                      | ? [X4,X5,X6,X7] :
                          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) != k1_binop_1(X3,X4,X5)
                          & r2_hidden(X7,X5)
                          & r2_hidden(X6,X4)
                          & r2_hidden(X5,k8_eqrel_1(X0,X1))
                          & r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                    & ( ! [X4,X5,X6,X7] :
                          ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) = k1_binop_1(X3,X4,X5)
                          | ~ r2_hidden(X7,X5)
                          | ~ r2_hidden(X6,X4)
                          | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                          | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                      | k3_filter_1(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) = k1_binop_1(X3,X4,X5)
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_filter_1(X0,X1,X2) = X3
                  <=> ! [X4,X5,X6,X7] :
                        ( k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) = k1_binop_1(X3,X4,X5)
                        | ~ r2_hidden(X7,X5)
                        | ~ r2_hidden(X6,X4)
                        | ~ r2_hidden(X5,k8_eqrel_1(X0,X1))
                        | ~ r2_hidden(X4,k8_eqrel_1(X0,X1)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                  | ~ v1_funct_1(X3) )
              | ~ m2_filter_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
                      & v1_funct_2(X3,k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
                      & v1_funct_1(X3) )
                   => ( k3_filter_1(X0,X1,X2) = X3
                    <=> ! [X4,X5,X6,X7] :
                          ( ( r2_hidden(X7,X5)
                            & r2_hidden(X6,X4)
                            & r2_hidden(X5,k8_eqrel_1(X0,X1))
                            & r2_hidden(X4,k8_eqrel_1(X0,X1)) )
                         => k6_eqrel_1(X0,X0,X1,k1_binop_1(X2,X6,X7)) = k1_binop_1(X3,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',d4_filter_1)).

fof(f7739,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK4))
    | ~ spl14_1010 ),
    inference(avatar_component_clause,[],[f7738])).

fof(f7746,plain,
    ( spl14_16
    | spl14_540
    | ~ spl14_2
    | ~ spl14_1008 ),
    inference(avatar_split_clause,[],[f7745,f7735,f175,f2495,f275])).

fof(f7735,plain,
    ( spl14_1008
  <=> ! [X1,X3,X0,X2] :
        ( ~ m2_filter_1(sK4,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1008])])).

fof(f7745,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(sK0) )
    | ~ spl14_2
    | ~ spl14_1008 ),
    inference(resolution,[],[f7736,f176])).

fof(f7736,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m2_filter_1(sK4,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X0) )
    | ~ spl14_1008 ),
    inference(avatar_component_clause,[],[f7735])).

fof(f7740,plain,
    ( spl14_540
    | ~ spl14_543
    | spl14_1008
    | spl14_1010
    | ~ spl14_2
    | ~ spl14_974 ),
    inference(avatar_split_clause,[],[f7729,f7174,f175,f7738,f7735,f7732,f2495])).

fof(f7732,plain,
    ( spl14_543
  <=> ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_543])])).

fof(f7174,plain,
    ( spl14_974
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
        | ~ v1_relat_1(X5)
        | ~ m2_filter_1(X0,sK0,X5)
        | ~ m2_filter_1(X0,X4,X1)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_974])])).

fof(f7729,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k3_filter_1(sK0,sK1,sK4))
        | ~ m2_filter_1(sK4,X0,X1)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl14_2
    | ~ spl14_974 ),
    inference(resolution,[],[f7177,f176])).

fof(f7177,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ m2_filter_1(X0,sK0,X1)
        | v1_funct_1(k3_filter_1(sK0,sK1,X0))
        | ~ m2_filter_1(X0,X2,X3)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl14_974 ),
    inference(resolution,[],[f7175,f156])).

fof(f7175,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_relat_1(X5)
        | v1_funct_1(k3_filter_1(sK0,sK1,X0))
        | ~ m2_filter_1(X0,sK0,X5)
        | ~ m2_filter_1(X0,X4,X1)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl14_974 ),
    inference(avatar_component_clause,[],[f7174])).

fof(f7176,plain,
    ( spl14_16
    | spl14_974
    | ~ spl14_972 ),
    inference(avatar_split_clause,[],[f7172,f7169,f7174,f275])).

fof(f7169,plain,
    ( spl14_972
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k3_filter_1(sK0,sK1,X4))
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | v1_xboole_0(X3)
        | ~ m2_filter_1(X4,X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_972])])).

fof(f7172,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | v1_xboole_0(X4)
        | ~ m2_filter_1(X0,X4,X1)
        | ~ m2_filter_1(X0,sK0,X5)
        | ~ v1_relat_1(X5)
        | v1_xboole_0(sK0) )
    | ~ spl14_972 ),
    inference(resolution,[],[f7170,f147])).

fof(f7170,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | v1_funct_1(k3_filter_1(sK0,sK1,X4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | v1_xboole_0(X3)
        | ~ m2_filter_1(X4,X3,X0) )
    | ~ spl14_972 ),
    inference(avatar_component_clause,[],[f7169])).

fof(f7171,plain,
    ( ~ spl14_15
    | spl14_16
    | spl14_972
    | ~ spl14_8
    | ~ spl14_928 ),
    inference(avatar_split_clause,[],[f7167,f6129,f187,f7169,f275,f851])).

fof(f6129,plain,
    ( spl14_928
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_funct_1(k3_filter_1(X0,sK1,X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ m2_filter_1(X1,X2,X3)
        | v1_xboole_0(X0)
        | ~ v1_partfun1(sK1,X0)
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_928])])).

fof(f7167,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ m2_filter_1(X4,X3,X0)
        | v1_xboole_0(sK0)
        | ~ v1_partfun1(sK1,sK0)
        | ~ v1_funct_2(X4,k2_zfmisc_1(sK0,sK0),sK0)
        | v1_funct_1(k3_filter_1(sK0,sK1,X4)) )
    | ~ spl14_8
    | ~ spl14_928 ),
    inference(resolution,[],[f6130,f188])).

fof(f6130,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | ~ m2_filter_1(X1,X2,X3)
        | v1_xboole_0(X0)
        | ~ v1_partfun1(sK1,X0)
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | v1_funct_1(k3_filter_1(X0,sK1,X1)) )
    | ~ spl14_928 ),
    inference(avatar_component_clause,[],[f6129])).

fof(f6131,plain,
    ( ~ spl14_13
    | spl14_928
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f6127,f191,f6129,f835])).

fof(f191,plain,
    ( spl14_10
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f6127,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k3_filter_1(X0,sK1,X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        | ~ v3_relat_2(sK1)
        | ~ v1_partfun1(sK1,X0)
        | v1_xboole_0(X0)
        | ~ m2_filter_1(X1,X2,X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl14_10 ),
    inference(resolution,[],[f2878,f192])).

fof(f192,plain,
    ( v8_relat_2(sK1)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f2878,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ v8_relat_2(X2)
      | v1_funct_1(k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m2_filter_1(X0,X3,X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f1648,f156])).

fof(f1648,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X4)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_funct_1(k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m2_filter_1(X0,X3,X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f159,f146])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f6044,plain,
    ( spl14_16
    | spl14_906
    | ~ spl14_904 ),
    inference(avatar_split_clause,[],[f6040,f6037,f6042,f275])).

fof(f6037,plain,
    ( spl14_904
  <=> ! [X0] :
        ( r2_hidden(X0,k11_relat_1(sK1,X0))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_904])])).

fof(f6040,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k11_relat_1(sK1,X0))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_904 ),
    inference(resolution,[],[f6038,f141])).

fof(f6038,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k11_relat_1(sK1,X0)) )
    | ~ spl14_904 ),
    inference(avatar_component_clause,[],[f6037])).

fof(f6039,plain,
    ( ~ spl14_15
    | spl14_904
    | ~ spl14_8
    | ~ spl14_836 ),
    inference(avatar_split_clause,[],[f6035,f4962,f187,f6037,f851])).

fof(f4962,plain,
    ( spl14_836
  <=> ! [X1,X0] :
        ( ~ v1_partfun1(sK1,X0)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | r2_hidden(X1,k6_eqrel_1(X0,X0,sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_836])])).

fof(f6035,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k11_relat_1(sK1,X0))
        | ~ r2_hidden(X0,sK0)
        | ~ v1_partfun1(sK1,sK0) )
    | ~ spl14_8
    | ~ spl14_836 ),
    inference(forward_demodulation,[],[f6034,f711])).

fof(f6034,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_partfun1(sK1,sK0)
        | r2_hidden(X0,k6_eqrel_1(sK0,sK0,sK1,X0)) )
    | ~ spl14_8
    | ~ spl14_836 ),
    inference(resolution,[],[f4963,f188])).

fof(f4963,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ r2_hidden(X1,X0)
        | ~ v1_partfun1(sK1,X0)
        | r2_hidden(X1,k6_eqrel_1(X0,X0,sK1,X1)) )
    | ~ spl14_836 ),
    inference(avatar_component_clause,[],[f4962])).

fof(f4964,plain,
    ( spl14_540
    | ~ spl14_13
    | spl14_836
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f4960,f191,f4962,f835,f2495])).

fof(f4960,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_partfun1(sK1,X0)
        | ~ v3_relat_2(sK1)
        | r2_hidden(X1,k6_eqrel_1(X0,X0,sK1,X1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl14_10 ),
    inference(resolution,[],[f2676,f192])).

fof(f2676,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v8_relat_2(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v3_relat_2(X0)
      | r2_hidden(X2,k6_eqrel_1(X1,X1,X0,X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f1145,f156])).

fof(f1145,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(X2,X1)
      | ~ v3_relat_2(X2)
      | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
      | ~ v8_relat_2(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f1144])).

fof(f1144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(X2,X1)
      | ~ v3_relat_2(X2)
      | r2_hidden(X0,k6_eqrel_1(X1,X1,X2,X0))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f150,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc3_partfun1)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_2(X1)
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2))
          | ~ r2_hidden(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v3_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v3_relat_2(X1)
        & v1_relat_2(X1) )
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,k6_eqrel_1(X0,X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t28_eqrel_1)).

fof(f2580,plain,
    ( ~ spl14_8
    | ~ spl14_540 ),
    inference(avatar_contradiction_clause,[],[f2579])).

fof(f2579,plain,
    ( $false
    | ~ spl14_8
    | ~ spl14_540 ),
    inference(subsumption_resolution,[],[f188,f2496])).

fof(f2496,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl14_540 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2500,plain,
    ( spl14_540
    | spl14_16
    | spl14_542
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f2491,f175,f2498,f275,f2495])).

fof(f2491,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl14_2 ),
    inference(resolution,[],[f760,f176])).

fof(f2352,plain,
    ( spl14_16
    | ~ spl14_13
    | ~ spl14_11
    | ~ spl14_15
    | ~ spl14_9
    | spl14_504
    | ~ spl14_498 ),
    inference(avatar_split_clause,[],[f2340,f2334,f2350,f1229,f851,f1226,f835,f275])).

fof(f2334,plain,
    ( spl14_498
  <=> ! [X0] :
        ( m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_498])])).

fof(f2340,plain,
    ( ! [X0] :
        ( m2_subset_1(k11_relat_1(sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_partfun1(sK1,sK0)
        | ~ v8_relat_2(sK1)
        | ~ v3_relat_2(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl14_498 ),
    inference(duplicate_literal_removal,[],[f2339])).

fof(f2339,plain,
    ( ! [X0] :
        ( m2_subset_1(k11_relat_1(sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_partfun1(sK1,sK0)
        | ~ v8_relat_2(sK1)
        | ~ v3_relat_2(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl14_498 ),
    inference(superposition,[],[f2335,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k9_eqrel_1)).

fof(f2335,plain,
    ( ! [X0] :
        ( m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_498 ),
    inference(avatar_component_clause,[],[f2334])).

fof(f2336,plain,
    ( ~ spl14_15
    | spl14_498
    | spl14_16
    | ~ spl14_8
    | ~ spl14_358 ),
    inference(avatar_split_clause,[],[f2332,f1496,f187,f275,f2334,f851])).

fof(f1496,plain,
    ( spl14_358
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
        | ~ v1_partfun1(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_358])])).

fof(f2332,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ v1_partfun1(sK1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl14_8
    | ~ spl14_358 ),
    inference(resolution,[],[f1497,f188])).

fof(f1497,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | v1_xboole_0(X1)
        | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
        | ~ v1_partfun1(sK1,X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl14_358 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1559,plain,
    ( ~ spl14_13
    | ~ spl14_11
    | ~ spl14_15
    | ~ spl14_9
    | spl14_158
    | ~ spl14_290 ),
    inference(avatar_split_clause,[],[f1546,f1207,f865,f1229,f851,f1226,f835])).

fof(f1207,plain,
    ( spl14_290
  <=> v1_xboole_0(k7_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_290])])).

fof(f1546,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ spl14_290 ),
    inference(superposition,[],[f1208,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',redefinition_k8_eqrel_1)).

fof(f1208,plain,
    ( v1_xboole_0(k7_eqrel_1(sK0,sK1))
    | ~ spl14_290 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1528,plain,(
    ~ spl14_360 ),
    inference(avatar_contradiction_clause,[],[f1525])).

fof(f1525,plain,
    ( $false
    | ~ spl14_360 ),
    inference(resolution,[],[f1511,f137])).

fof(f1511,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k7_eqrel_1(sK0,sK1))
    | ~ spl14_360 ),
    inference(avatar_component_clause,[],[f1510])).

fof(f1510,plain,
    ( spl14_360
  <=> ! [X0] : ~ m1_subset_1(X0,k7_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_360])])).

fof(f1512,plain,
    ( spl14_360
    | spl14_290
    | ~ spl14_26
    | ~ spl14_28
    | ~ spl14_332 ),
    inference(avatar_split_clause,[],[f1502,f1344,f244,f235,f1207,f1510])).

fof(f235,plain,
    ( spl14_26
  <=> v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f244,plain,
    ( spl14_28
  <=> o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f1344,plain,
    ( spl14_332
  <=> m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_332])])).

fof(f1502,plain,
    ( ! [X0] :
        ( v1_xboole_0(k7_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,k7_eqrel_1(sK0,sK1)) )
    | ~ spl14_26
    | ~ spl14_28
    | ~ spl14_332 ),
    inference(resolution,[],[f1345,f297])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl14_26
    | ~ spl14_28 ),
    inference(forward_demodulation,[],[f296,f245])).

fof(f245,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(o_0_0_xboole_0))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl14_26 ),
    inference(resolution,[],[f238,f141])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(o_0_0_xboole_0)))) )
    | ~ spl14_26 ),
    inference(resolution,[],[f236,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t5_subset)).

fof(f236,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f235])).

fof(f1345,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl14_332 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1498,plain,
    ( ~ spl14_13
    | spl14_358
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f1494,f191,f1496,f835])).

fof(f1494,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v1_partfun1(sK1,X1)
        | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
        | ~ v3_relat_2(sK1)
        | v1_xboole_0(X1) )
    | ~ spl14_10 ),
    inference(resolution,[],[f158,f192])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k9_eqrel_1)).

fof(f1488,plain,
    ( spl14_16
    | ~ spl14_18
    | ~ spl14_336 ),
    inference(avatar_split_clause,[],[f1483,f1417,f207,f275])).

fof(f207,plain,
    ( spl14_18
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f1417,plain,
    ( spl14_336
  <=> m1_eqrel_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_336])])).

fof(f1483,plain,
    ( v1_xboole_0(sK0)
    | ~ spl14_18
    | ~ spl14_336 ),
    inference(resolution,[],[f1418,f221])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_eqrel_1(o_0_0_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl14_18 ),
    inference(resolution,[],[f126,f208])).

fof(f208,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',cc1_eqrel_1)).

fof(f1418,plain,
    ( m1_eqrel_1(o_0_0_xboole_0,sK0)
    | ~ spl14_336 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1419,plain,
    ( spl14_336
    | ~ spl14_154
    | ~ spl14_334 ),
    inference(avatar_split_clause,[],[f1390,f1370,f854,f1417])).

fof(f854,plain,
    ( spl14_154
  <=> m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_154])])).

fof(f1370,plain,
    ( spl14_334
  <=> k8_eqrel_1(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_334])])).

fof(f1390,plain,
    ( m1_eqrel_1(o_0_0_xboole_0,sK0)
    | ~ spl14_154
    | ~ spl14_334 ),
    inference(superposition,[],[f855,f1371])).

fof(f1371,plain,
    ( k8_eqrel_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl14_334 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f855,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl14_154 ),
    inference(avatar_component_clause,[],[f854])).

fof(f1373,plain,
    ( spl14_334
    | ~ spl14_18
    | ~ spl14_158 ),
    inference(avatar_split_clause,[],[f1363,f865,f207,f1370])).

fof(f1363,plain,
    ( k8_eqrel_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl14_18
    | ~ spl14_158 ),
    inference(resolution,[],[f866,f222])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl14_18 ),
    inference(resolution,[],[f154,f208])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t8_boole)).

fof(f866,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl14_158 ),
    inference(avatar_component_clause,[],[f865])).

fof(f1346,plain,
    ( spl14_332
    | ~ spl14_168
    | ~ spl14_288 ),
    inference(avatar_split_clause,[],[f1264,f1198,f895,f1344])).

fof(f895,plain,
    ( spl14_168
  <=> k1_zfmisc_1(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).

fof(f1198,plain,
    ( spl14_288
  <=> m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_288])])).

fof(f1264,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl14_168
    | ~ spl14_288 ),
    inference(superposition,[],[f1199,f896])).

fof(f896,plain,
    ( k1_zfmisc_1(sK0) = o_0_0_xboole_0
    | ~ spl14_168 ),
    inference(avatar_component_clause,[],[f895])).

fof(f1199,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl14_288 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f1234,plain,
    ( ~ spl14_13
    | ~ spl14_11
    | ~ spl14_15
    | ~ spl14_9
    | spl14_300
    | ~ spl14_288 ),
    inference(avatar_split_clause,[],[f1205,f1198,f1232,f1229,f851,f1226,f835])).

fof(f1232,plain,
    ( spl14_300
  <=> m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_300])])).

fof(f1205,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ spl14_288 ),
    inference(superposition,[],[f1199,f152])).

fof(f1200,plain,
    ( ~ spl14_15
    | spl14_288
    | ~ spl14_8
    | ~ spl14_242 ),
    inference(avatar_split_clause,[],[f1196,f1098,f187,f1198,f851])).

fof(f1098,plain,
    ( spl14_242
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ v1_partfun1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_242])])).

fof(f1196,plain,
    ( m1_subset_1(k7_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v1_partfun1(sK1,sK0)
    | ~ spl14_8
    | ~ spl14_242 ),
    inference(resolution,[],[f1099,f188])).

fof(f1099,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ v1_partfun1(sK1,X0) )
    | ~ spl14_242 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1100,plain,
    ( ~ spl14_13
    | spl14_242
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f1096,f191,f1098,f835])).

fof(f1096,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(sK1,X0)
        | m1_subset_1(k7_eqrel_1(X0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ v3_relat_2(sK1) )
    | ~ spl14_10 ),
    inference(resolution,[],[f153,f192])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_subset_1(k7_eqrel_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k7_eqrel_1)).

fof(f898,plain,
    ( spl14_168
    | ~ spl14_18
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f887,f479,f207,f895])).

fof(f887,plain,
    ( k1_zfmisc_1(sK0) = o_0_0_xboole_0
    | ~ spl14_18
    | ~ spl14_96 ),
    inference(resolution,[],[f480,f222])).

fof(f480,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f479])).

fof(f856,plain,
    ( ~ spl14_15
    | spl14_154
    | ~ spl14_8
    | ~ spl14_148 ),
    inference(avatar_split_clause,[],[f849,f838,f187,f854,f851])).

fof(f838,plain,
    ( spl14_148
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_eqrel_1(k8_eqrel_1(X0,sK1),X0)
        | ~ v1_partfun1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_148])])).

fof(f849,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ v1_partfun1(sK1,sK0)
    | ~ spl14_8
    | ~ spl14_148 ),
    inference(resolution,[],[f839,f188])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | m1_eqrel_1(k8_eqrel_1(X0,sK1),X0)
        | ~ v1_partfun1(sK1,X0) )
    | ~ spl14_148 ),
    inference(avatar_component_clause,[],[f838])).

fof(f840,plain,
    ( ~ spl14_13
    | spl14_148
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f833,f191,f838,f835])).

fof(f833,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(sK1,X0)
        | m1_eqrel_1(k8_eqrel_1(X0,sK1),X0)
        | ~ v3_relat_2(sK1) )
    | ~ spl14_10 ),
    inference(resolution,[],[f151,f192])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_k8_eqrel_1)).

fof(f747,plain,
    ( ~ spl14_137
    | spl14_1
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f746,f187,f171,f742])).

fof(f171,plain,
    ( spl14_1
  <=> k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f746,plain,
    ( k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3)) != k11_relat_1(sK1,k4_binop_1(sK0,sK4,sK2,sK3))
    | ~ spl14_1
    | ~ spl14_8 ),
    inference(forward_demodulation,[],[f745,f711])).

fof(f745,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k11_relat_1(sK1,sK2),k11_relat_1(sK1,sK3))
    | ~ spl14_1
    | ~ spl14_8 ),
    inference(forward_demodulation,[],[f725,f711])).

fof(f725,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k11_relat_1(sK1,sK3))
    | ~ spl14_1
    | ~ spl14_8 ),
    inference(superposition,[],[f172,f711])).

fof(f172,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3))
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f171])).

fof(f246,plain,
    ( spl14_28
    | ~ spl14_18
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f239,f235,f207,f244])).

fof(f239,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl14_18
    | ~ spl14_26 ),
    inference(resolution,[],[f236,f222])).

fof(f237,plain,
    ( spl14_24
    | spl14_26
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f230,f207,f235,f232])).

fof(f230,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK10(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl14_18 ),
    inference(resolution,[],[f229,f141])).

fof(f229,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl14_18 ),
    inference(resolution,[],[f228,f137])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl14_18 ),
    inference(resolution,[],[f163,f208])).

fof(f209,plain,(
    spl14_18 ),
    inference(avatar_split_clause,[],[f125,f207])).

fof(f125,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',dt_o_0_0_xboole_0)).

fof(f205,plain,(
    ~ spl14_17 ),
    inference(avatar_split_clause,[],[f116,f203])).

fof(f203,plain,
    ( spl14_17
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f116,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,
    ( k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3))
    & m2_filter_1(sK4,sK0,sK1)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f47,f99,f98,f97,f96,f95])).

fof(f95,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
                        & m2_filter_1(X4,X0,X1) )
                    & m1_subset_1(X3,X0) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k6_eqrel_1(sK0,sK0,X1,k4_binop_1(sK0,X4,X2,X3)) != k1_binop_1(k3_filter_1(sK0,X1,X4),k6_eqrel_1(sK0,sK0,X1,X2),k6_eqrel_1(sK0,sK0,X1,X3))
                      & m2_filter_1(X4,sK0,X1) )
                  & m1_subset_1(X3,sK0) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k6_eqrel_1(X0,X0,sK1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,sK1,X4),k6_eqrel_1(X0,X0,sK1,X2),k6_eqrel_1(X0,X0,sK1,X3))
                    & m2_filter_1(X4,X0,sK1) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK1)
        & v3_relat_2(sK1)
        & v1_partfun1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
                  & m2_filter_1(X4,X0,X1) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,sK2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,sK2),k6_eqrel_1(X0,X0,X1,X3))
                & m2_filter_1(X4,X0,X1) )
            & m1_subset_1(X3,X0) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
              & m2_filter_1(X4,X0,X1) )
          & m1_subset_1(X3,X0) )
     => ( ? [X4] :
            ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,sK3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,sK3))
            & m2_filter_1(X4,X0,X1) )
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
          & m2_filter_1(X4,X0,X1) )
     => ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,sK4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,sK4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
        & m2_filter_1(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) != k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3))
                      & m2_filter_1(X4,X0,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ! [X4] :
                        ( m2_filter_1(X4,X0,X1)
                       => k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) = k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ! [X4] :
                      ( m2_filter_1(X4,X0,X1)
                     => k6_eqrel_1(X0,X0,X1,k4_binop_1(X0,X4,X2,X3)) = k1_binop_1(k3_filter_1(X0,X1,X4),k6_eqrel_1(X0,X0,X1,X2),k6_eqrel_1(X0,X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t3_filter_1.p',t3_filter_1)).

fof(f201,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f117,f199])).

fof(f199,plain,
    ( spl14_14
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f117,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f197,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f118,f195])).

fof(f195,plain,
    ( spl14_12
  <=> v3_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f118,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f100])).

fof(f193,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f119,f191])).

fof(f119,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f100])).

fof(f189,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f120,f187])).

fof(f120,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f100])).

fof(f185,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f121,f183])).

fof(f183,plain,
    ( spl14_6
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f121,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f181,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f122,f179])).

fof(f179,plain,
    ( spl14_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f122,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f177,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f123,f175])).

fof(f123,plain,(
    m2_filter_1(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f100])).

fof(f173,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f124,f171])).

fof(f124,plain,(
    k6_eqrel_1(sK0,sK0,sK1,k4_binop_1(sK0,sK4,sK2,sK3)) != k1_binop_1(k3_filter_1(sK0,sK1,sK4),k6_eqrel_1(sK0,sK0,sK1,sK2),k6_eqrel_1(sK0,sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f100])).
%------------------------------------------------------------------------------
