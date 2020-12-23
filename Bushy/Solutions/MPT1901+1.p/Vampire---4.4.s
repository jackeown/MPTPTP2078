%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t69_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:55 EDT 2019

% Result     : Theorem 106.42s
% Output     : Refutation 106.42s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 869 expanded)
%              Number of leaves         :   35 ( 251 expanded)
%              Depth                    :   57
%              Number of atoms          :  945 (2476 expanded)
%              Number of equality atoms :   53 ( 576 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f164,f171,f178,f231,f2389,f8959,f16327,f16757])).

fof(f16757,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_46 ),
    inference(avatar_contradiction_clause,[],[f16756])).

fof(f16756,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f16755,f170])).

fof(f170,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f16755,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f16754,f163])).

fof(f163,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f16754,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f16752,f156])).

fof(f156,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl7_1
  <=> ~ v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f16752,plain,
    ( v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_46 ),
    inference(resolution,[],[f16326,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(sK1(X0),X0)
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f85,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t18_tdlat_3)).

fof(f16326,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f16325])).

fof(f16325,plain,
    ( spl7_46
  <=> v4_pre_topc(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f16327,plain,
    ( spl7_46
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_31 ),
    inference(avatar_split_clause,[],[f16320,f877,f169,f162,f155,f16325])).

fof(f877,plain,
    ( spl7_31
  <=> ~ v2_struct_0(k1_compts_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f16320,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f16319,f170])).

fof(f16319,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f16318,f163])).

fof(f16318,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f16271,f156])).

fof(f16271,plain,
    ( v4_pre_topc(sK1(sK0),sK0)
    | v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(resolution,[],[f16157,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f16157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(duplicate_literal_removal,[],[f16156])).

fof(f16156,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(superposition,[],[f16133,f344])).

fof(f344,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f340,f125])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k6_partfun1)).

fof(f340,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f141,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t171_funct_2)).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k8_relset_1)).

fof(f16133,plain,
    ( ! [X7] :
        ( v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(sK0)),X7),sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f16132,f246])).

fof(f246,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(backward_demodulation,[],[f147,f129])).

fof(f129,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc3_funct_1)).

fof(f147,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k6_partfun1)).

fof(f16132,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(sK0)),X7),sK0)
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f16131,f878])).

fof(f878,plain,
    ( ~ v2_struct_0(k1_compts_1(u1_struct_0(sK0)))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f877])).

fof(f16131,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(k1_compts_1(u1_struct_0(sK0)))
        | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(sK0)),X7),sK0)
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f16090,f124])).

fof(f124,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16090,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_partfun1(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0))
        | v2_struct_0(k1_compts_1(u1_struct_0(sK0)))
        | v4_pre_topc(k10_relat_1(k6_partfun1(u1_struct_0(sK0)),X7),sK0)
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0))) )
    | ~ spl7_2 ),
    inference(resolution,[],[f16080,f125])).

fof(f16080,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ v1_partfun1(X1,u1_struct_0(sK0))
        | v2_struct_0(k1_compts_1(X0))
        | v4_pre_topc(k10_relat_1(X1,X2),sK0)
        | ~ v1_funct_1(X1) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f16079])).

fof(f16079,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ v1_partfun1(X1,u1_struct_0(sK0))
        | v2_struct_0(k1_compts_1(X0))
        | v4_pre_topc(k10_relat_1(X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f15987,f344])).

fof(f15987,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X0)),X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ v1_partfun1(X1,u1_struct_0(sK0))
        | v2_struct_0(k1_compts_1(X0))
        | v4_pre_topc(k10_relat_1(X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f15986])).

fof(f15986,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X0)),X1))
        | v2_struct_0(k1_compts_1(X0))
        | v4_pre_topc(k10_relat_1(X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f15947,f344])).

fof(f15947,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X0)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X0)),X1))
        | v2_struct_0(k1_compts_1(X0))
        | v4_pre_topc(k10_relat_1(X1,X2),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f15892,f344])).

fof(f15892,plain,
    ( ! [X4,X5,X3] :
        ( v4_pre_topc(k10_relat_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4))
        | v2_struct_0(k1_compts_1(X3))
        | ~ v1_partfun1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f15890])).

fof(f15890,plain,
    ( ! [X4,X5,X3] :
        ( v4_pre_topc(k10_relat_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4))
        | v2_struct_0(k1_compts_1(X3))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4))
        | ~ v1_partfun1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f15851,f440])).

fof(f440,plain,(
    ! [X21,X22,X20] :
      ( v1_funct_2(k10_relat_1(k6_partfun1(k2_zfmisc_1(X20,X21)),X22),X20,X21)
      | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(X20,X21)),X22))
      | ~ v1_partfun1(k10_relat_1(k6_partfun1(k2_zfmisc_1(X20,X21)),X22),X20) ) ),
    inference(resolution,[],[f426,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',cc1_funct_2)).

fof(f426,plain,(
    ! [X10,X9] : m1_subset_1(k10_relat_1(k6_partfun1(X9),X10),k1_zfmisc_1(X9)) ),
    inference(resolution,[],[f343,f125])).

fof(f343,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k10_relat_1(X4,X5),k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k10_relat_1(X4,X5),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(superposition,[],[f114,f141])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k8_relset_1)).

fof(f15851,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),u1_struct_0(sK0),X3)
        | v4_pre_topc(k10_relat_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
        | ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4))
        | v2_struct_0(k1_compts_1(X3)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f15850,f125])).

fof(f15850,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4))
        | v4_pre_topc(k10_relat_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
        | ~ v1_funct_2(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),X4),u1_struct_0(sK0),X3)
        | v2_struct_0(k1_compts_1(X3))
        | ~ m1_subset_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X3)),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),k2_zfmisc_1(u1_struct_0(sK0),X3)))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f15753,f141])).

fof(f15753,plain,
    ( ! [X12,X13,X11] :
        ( ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X11),k2_zfmisc_1(u1_struct_0(sK0),X11),k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X11)),X12))
        | v4_pre_topc(k10_relat_1(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X11)),X12),X13),sK0)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ v1_funct_2(k10_relat_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),X11)),X12),u1_struct_0(sK0),X11)
        | v2_struct_0(k1_compts_1(X11)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f15720,f125])).

fof(f15720,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4)))
        | v4_pre_topc(k10_relat_1(k10_relat_1(X5,X6),X7),sK0)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X3))
        | ~ v1_funct_2(k10_relat_1(X5,X6),u1_struct_0(sK0),X3)
        | v2_struct_0(k1_compts_1(X3)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f15719])).

fof(f15719,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( v4_pre_topc(k10_relat_1(k10_relat_1(X5,X6),X7),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X3))
        | ~ v1_funct_2(k10_relat_1(X5,X6),u1_struct_0(sK0),X3)
        | v2_struct_0(k1_compts_1(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f15679,f141])).

fof(f15679,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6),X7),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X3))
        | ~ v1_funct_2(k10_relat_1(X5,X6),u1_struct_0(sK0),X3)
        | v2_struct_0(k1_compts_1(X3)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f15678])).

fof(f15678,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ v1_funct_2(k10_relat_1(X5,X6),u1_struct_0(sK0),X3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(X3))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4,X5,X6),X7),sK0)
        | v2_struct_0(k1_compts_1(X3))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X3),X4))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f14668,f141])).

fof(f14668,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | v2_struct_0(k1_compts_1(X5)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14667,f1112])).

fof(f1112,plain,(
    ! [X0] : g1_pre_topc(X0,u1_pre_topc(k1_compts_1(X0))) = k1_compts_1(X0) ),
    inference(backward_demodulation,[],[f931,f277])).

fof(f277,plain,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k1_zfmisc_1(X0))) = k1_compts_1(X0) ),
    inference(forward_demodulation,[],[f140,f146])).

fof(f146,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',redefinition_k9_setfam_1)).

fof(f140,plain,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) = k1_compts_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : g1_pre_topc(X0,k2_subset_1(k9_setfam_1(X0))) = k1_compts_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',d8_compts_1)).

fof(f931,plain,(
    ! [X0] : u1_pre_topc(k1_compts_1(X0)) = k2_subset_1(k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f930,f134])).

fof(f134,plain,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : l1_pre_topc(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k1_compts_1)).

fof(f930,plain,(
    ! [X0] :
      ( u1_pre_topc(k1_compts_1(X0)) = k2_subset_1(k1_zfmisc_1(X0))
      | ~ l1_pre_topc(k1_compts_1(X0)) ) ),
    inference(subsumption_resolution,[],[f929,f289])).

fof(f289,plain,(
    ! [X2] : v1_pre_topc(k1_compts_1(X2)) ),
    inference(forward_demodulation,[],[f287,f277])).

fof(f287,plain,(
    ! [X2] : v1_pre_topc(g1_pre_topc(X2,k2_subset_1(k1_zfmisc_1(X2)))) ),
    inference(resolution,[],[f131,f149])).

fof(f149,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_k2_subset_1)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_g1_pre_topc)).

fof(f929,plain,(
    ! [X0] :
      ( u1_pre_topc(k1_compts_1(X0)) = k2_subset_1(k1_zfmisc_1(X0))
      | ~ v1_pre_topc(k1_compts_1(X0))
      | ~ l1_pre_topc(k1_compts_1(X0)) ) ),
    inference(equality_resolution,[],[f417])).

fof(f417,plain,(
    ! [X2,X3] :
      ( k1_compts_1(X3) != X2
      | u1_pre_topc(X2) = k2_subset_1(k1_zfmisc_1(X3))
      | ~ v1_pre_topc(X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f330,f127])).

fof(f127,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',abstractness_v1_pre_topc)).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X1,X2) != k1_compts_1(X0)
      | k2_subset_1(k1_zfmisc_1(X0)) = X2 ) ),
    inference(subsumption_resolution,[],[f325,f149])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X1,X2) != k1_compts_1(X0)
      | k2_subset_1(k1_zfmisc_1(X0)) = X2
      | ~ m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f118,f277])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',free_g1_pre_topc)).

fof(f14667,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f14666,f248])).

fof(f248,plain,(
    ! [X0] : v2_pre_topc(k1_compts_1(X0)) ),
    inference(subsumption_resolution,[],[f247,f134])).

fof(f247,plain,(
    ! [X0] :
      ( v2_pre_topc(k1_compts_1(X0))
      | ~ l1_pre_topc(k1_compts_1(X0)) ) ),
    inference(resolution,[],[f108,f109])).

fof(f109,plain,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : v1_tdlat_3(k1_compts_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc4_tex_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',cc1_tdlat_3)).

fof(f14666,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v2_pre_topc(k1_compts_1(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14665,f1112])).

fof(f14665,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f14664,f289])).

fof(f14664,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_pre_topc(k1_compts_1(X5))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14663,f1112])).

fof(f14663,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14662,f671])).

fof(f671,plain,(
    ! [X0] : u1_struct_0(k1_compts_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f670,f134])).

fof(f670,plain,(
    ! [X0] :
      ( u1_struct_0(k1_compts_1(X0)) = X0
      | ~ l1_pre_topc(k1_compts_1(X0)) ) ),
    inference(subsumption_resolution,[],[f669,f289])).

fof(f669,plain,(
    ! [X0] :
      ( u1_struct_0(k1_compts_1(X0)) = X0
      | ~ v1_pre_topc(k1_compts_1(X0))
      | ~ l1_pre_topc(k1_compts_1(X0)) ) ),
    inference(equality_resolution,[],[f398])).

fof(f398,plain,(
    ! [X2,X3] :
      ( k1_compts_1(X3) != X2
      | u1_struct_0(X2) = X3
      | ~ v1_pre_topc(X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f323,f127])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X1,X2) != k1_compts_1(X0)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f318,f149])).

fof(f318,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(X1,X2) != k1_compts_1(X0)
      | X0 = X1
      | ~ m1_subset_1(k2_subset_1(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f117,f277])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f14662,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k1_compts_1(X5))),X6)))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14661,f1112])).

fof(f14661,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f14660,f134])).

fof(f14660,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ l1_pre_topc(k1_compts_1(X5))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14659,f1112])).

fof(f14659,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14658,f671])).

fof(f14658,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k1_compts_1(X5))),X6,X7,X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14657,f1112])).

fof(f14657,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f14656,f765])).

fof(f765,plain,(
    ! [X43,X42] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | v4_pre_topc(X43,k1_compts_1(X42)) ) ),
    inference(subsumption_resolution,[],[f764,f134])).

fof(f764,plain,(
    ! [X43,X42] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | v4_pre_topc(X43,k1_compts_1(X42))
      | ~ l1_pre_topc(k1_compts_1(X42)) ) ),
    inference(subsumption_resolution,[],[f693,f109])).

fof(f693,plain,(
    ! [X43,X42] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | v4_pre_topc(X43,k1_compts_1(X42))
      | ~ v1_tdlat_3(k1_compts_1(X42))
      | ~ l1_pre_topc(k1_compts_1(X42)) ) ),
    inference(superposition,[],[f304,f671])).

fof(f304,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f105,f108])).

fof(f105,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f14656,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ v4_pre_topc(X9,k1_compts_1(X5))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14655,f1112])).

fof(f14655,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(X5))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v4_pre_topc(X9,g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14654,f671])).

fof(f14654,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(k1_compts_1(X5))))
        | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ v4_pre_topc(X9,g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14653,f1112])).

fof(f14653,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))))
        | ~ v4_pre_topc(X9,g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f14641,f671])).

fof(f14641,plain,
    ( ! [X6,X8,X7,X5,X9] :
        ( v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k1_compts_1(X5))),X6,X7,X8),X9),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X5),X6,X7,X8),u1_struct_0(sK0),X5)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))))
        | ~ v4_pre_topc(X9,g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6,X7,X8))
        | ~ l1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))),X6)))
        | ~ v1_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | ~ v2_pre_topc(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5))))
        | v2_struct_0(g1_pre_topc(X5,u1_pre_topc(k1_compts_1(X5)))) )
    | ~ spl7_2 ),
    inference(superposition,[],[f8380,f1112])).

fof(f8380,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5),X0),sK0)
        | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X1),X3,X4,X5),u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
        | ~ v4_pre_topc(X0,g1_pre_topc(X1,X2))
        | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5))
        | ~ l1_pre_topc(g1_pre_topc(X1,X2))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3)))
        | ~ v1_pre_topc(g1_pre_topc(X1,X2))
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | v2_struct_0(g1_pre_topc(X1,X2)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f8379,f163])).

fof(f8379,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X1),X3,X4,X5),u1_struct_0(sK0),X1)
      | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5),X0),sK0)
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,X2))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5))
      | ~ l1_pre_topc(g1_pre_topc(X1,X2))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3)))
      | ~ v1_pre_topc(g1_pre_topc(X1,X2))
      | ~ v2_pre_topc(g1_pre_topc(X1,X2))
      | v2_struct_0(g1_pre_topc(X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f8334])).

fof(f8334,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2))))
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X1),X3,X4,X5),u1_struct_0(sK0),X1)
      | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5),X0),sK0)
      | ~ v4_pre_topc(X0,g1_pre_topc(X1,X2))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5))
      | ~ l1_pre_topc(g1_pre_topc(X1,X2))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3)))
      | ~ v1_pre_topc(g1_pre_topc(X1,X2))
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X1),X3,X4,X5),u1_struct_0(sK0),X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3)))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X1,X2))),X3,X4,X5))
      | ~ l1_pre_topc(g1_pre_topc(X1,X2))
      | ~ v2_pre_topc(g1_pre_topc(X1,X2))
      | v2_struct_0(g1_pre_topc(X1,X2))
      | ~ v1_pre_topc(g1_pre_topc(X1,X2)) ) ),
    inference(resolution,[],[f1663,f1009])).

fof(f1009,plain,(
    ! [X78,X76,X79,X77,X75] :
      ( v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77,X78,X79),sK0,g1_pre_topc(X75,X76))
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X75),X77,X78,X79),u1_struct_0(sK0),X75)
      | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77)))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77,X78,X79))
      | ~ l1_pre_topc(g1_pre_topc(X75,X76))
      | ~ v2_pre_topc(g1_pre_topc(X75,X76))
      | v2_struct_0(g1_pre_topc(X75,X76))
      | ~ v1_pre_topc(g1_pre_topc(X75,X76)) ) ),
    inference(duplicate_literal_removal,[],[f958])).

fof(f958,plain,(
    ! [X78,X76,X79,X77,X75] :
      ( ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),X75),X77,X78,X79),u1_struct_0(sK0),X75)
      | v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77,X78,X79),sK0,g1_pre_topc(X75,X76))
      | ~ m1_subset_1(X78,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77)))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(X75,X76))),X77,X78,X79))
      | ~ l1_pre_topc(g1_pre_topc(X75,X76))
      | ~ v2_pre_topc(g1_pre_topc(X75,X76))
      | v2_struct_0(g1_pre_topc(X75,X76))
      | ~ v1_pre_topc(g1_pre_topc(X75,X76))
      | ~ l1_pre_topc(g1_pre_topc(X75,X76)) ) ),
    inference(superposition,[],[f313,f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( u1_struct_0(g1_pre_topc(X0,X1)) = X0
      | ~ v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(equality_resolution,[],[f324])).

fof(f324,plain,(
    ! [X4,X5,X3] :
      ( g1_pre_topc(X4,X5) != X3
      | u1_struct_0(X3) = X4
      | ~ v1_pre_topc(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f319,f128])).

fof(f128,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_u1_pre_topc)).

fof(f319,plain,(
    ! [X4,X5,X3] :
      ( g1_pre_topc(X4,X5) != X3
      | u1_struct_0(X3) = X4
      | ~ m1_subset_1(u1_pre_topc(X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ v1_pre_topc(X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f117,f127])).

fof(f313,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)),X16,X14,X17),u1_struct_0(sK0),u1_struct_0(X15))
      | v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)),X16,X14,X17),sK0,X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)),X16)))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)),X16,X14,X17))
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(resolution,[],[f114,f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(X2,sK0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ~ v1_tdlat_3(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( v5_pre_topc(X2,sK0,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            | ~ v1_funct_1(X2) )
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ~ v1_tdlat_3(X0)
        & ! [X1] :
            ( ! [X2] :
                ( v5_pre_topc(X2,X0,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                | ~ v1_funct_1(X2) )
            | ~ l1_pre_topc(X1)
            | ~ v2_pre_topc(X1)
            | v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v1_tdlat_3(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,sK0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ~ v1_tdlat_3(X0)
      & ! [X1] :
          ( ! [X2] :
              ( v5_pre_topc(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( ( l1_pre_topc(X1)
                & v2_pre_topc(X1)
                & ~ v2_struct_0(X1) )
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                 => v5_pre_topc(X2,X0,X1) ) )
         => v1_tdlat_3(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) )
       => v1_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',t69_tex_2)).

fof(f1663,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11),X8,g1_pre_topc(X6,X7))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X6,X7))))
      | ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),X6),X9,X10,X11),u1_struct_0(X8),X6)
      | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11),X12),X8)
      | ~ v4_pre_topc(X12,g1_pre_topc(X6,X7))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11))
      | ~ l1_pre_topc(g1_pre_topc(X6,X7))
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9)))
      | ~ v1_pre_topc(g1_pre_topc(X6,X7)) ) ),
    inference(duplicate_literal_removal,[],[f1662])).

fof(f1662,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),X6),X9,X10,X11),u1_struct_0(X8),X6)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X6,X7))))
      | ~ v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11),X8,g1_pre_topc(X6,X7))
      | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11),X12),X8)
      | ~ v4_pre_topc(X12,g1_pre_topc(X6,X7))
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9,X10,X11))
      | ~ l1_pre_topc(g1_pre_topc(X6,X7))
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(g1_pre_topc(X6,X7))),X9)))
      | ~ v1_pre_topc(g1_pre_topc(X6,X7))
      | ~ l1_pre_topc(g1_pre_topc(X6,X7)) ) ),
    inference(superposition,[],[f567,f452])).

fof(f567,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(k8_relset_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)),X3,X4,X5),u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(k8_relset_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)),X3,X4,X5),X2,X1)
      | v4_pre_topc(k10_relat_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)),X3,X4,X5),X0),X2)
      | ~ v4_pre_topc(X0,X1)
      | ~ v1_funct_1(k8_relset_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)),X3,X4,X5))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)),X3))) ) ),
    inference(resolution,[],[f369,f114])).

fof(f369,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v4_pre_topc(X5,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v5_pre_topc(X4,X2,X3)
      | v4_pre_topc(k10_relat_1(X4,X5),X2)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X4,X2,X5,X3] :
      ( v4_pre_topc(k10_relat_1(X4,X5),X2)
      | ~ v4_pre_topc(X5,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v5_pre_topc(X4,X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ) ),
    inference(superposition,[],[f110,f141])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
                    & v4_pre_topc(sK2(X0,X1,X2),X1)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
        & v4_pre_topc(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',d12_pre_topc)).

fof(f8959,plain,
    ( spl7_7
    | ~ spl7_20
    | ~ spl7_42 ),
    inference(avatar_contradiction_clause,[],[f8958])).

fof(f8958,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_20
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f8957,f177])).

fof(f177,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f8957,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_20
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f8952,f230])).

fof(f230,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl7_20
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f8952,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_42 ),
    inference(resolution,[],[f2388,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc2_struct_0)).

fof(f2388,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2387,plain,
    ( spl7_42
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f2389,plain,
    ( spl7_42
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f2382,f880,f2387])).

fof(f880,plain,
    ( spl7_30
  <=> v2_struct_0(k1_compts_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f2382,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(resolution,[],[f881,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k1_compts_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k1_compts_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',fc2_compts_1)).

fof(f881,plain,
    ( v2_struct_0(k1_compts_1(u1_struct_0(sK0)))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f880])).

fof(f231,plain,
    ( spl7_20
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f222,f162,f229])).

fof(f222,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f133,f163])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t69_tex_2.p',dt_l1_pre_topc)).

fof(f178,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f100,f176])).

fof(f100,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f171,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f101,f169])).

fof(f101,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f164,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f102,f162])).

fof(f102,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f157,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f104,f155])).

fof(f104,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------
