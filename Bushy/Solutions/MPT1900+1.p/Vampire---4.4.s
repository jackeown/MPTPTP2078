%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t68_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:55 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 378 expanded)
%              Number of leaves         :   46 ( 166 expanded)
%              Depth                    :   11
%              Number of atoms          :  536 (1656 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f106,f113,f120,f127,f134,f141,f148,f155,f165,f175,f184,f196,f217,f225,f252,f269,f290,f299,f310,f318,f377,f402,f418])).

fof(f418,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f416,f348])).

fof(f348,plain,
    ( ! [X0] : v4_pre_topc(k10_relat_1(sK2,X0),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f98,f112,f105,f346,f79])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t18_tdlat_3)).

fof(f346,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_22 ),
    inference(backward_demodulation,[],[f343,f320])).

fof(f320,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f183,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',dt_k8_relset_1)).

fof(f183,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f343,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f183,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',redefinition_k8_relset_1)).

fof(f105,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f112,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f416,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f414,f343])).

fof(f414,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f112,f126,f133,f154,f174,f183,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v4_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v4_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',d12_pre_topc)).

fof(f174,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl7_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f154,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_17
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f133,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f126,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f402,plain,
    ( spl7_46
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f394,f182,f173,f153,f132,f125,f111,f400])).

fof(f400,plain,
    ( spl7_46
  <=> m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f394,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f112,f126,f133,f154,f174,f183,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f377,plain,
    ( spl7_44
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f370,f182,f173,f153,f132,f125,f111,f375])).

fof(f375,plain,
    ( spl7_44
  <=> v4_pre_topc(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f370,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK1)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f112,f126,f133,f154,f174,f183,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK3(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f318,plain,
    ( ~ spl7_43
    | spl7_37 ),
    inference(avatar_split_clause,[],[f291,f288,f316])).

fof(f316,plain,
    ( spl7_43
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f288,plain,
    ( spl7_37
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f291,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f82,f289,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t4_subset)).

fof(f289,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f288])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',existence_m1_subset_1)).

fof(f310,plain,
    ( spl7_40
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f300,f111,f104,f97,f308])).

fof(f308,plain,
    ( spl7_40
  <=> v4_pre_topc(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f300,plain,
    ( v4_pre_topc(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f98,f112,f105,f82,f79])).

fof(f299,plain,
    ( ~ spl7_39
    | spl7_37 ),
    inference(avatar_split_clause,[],[f292,f288,f297])).

fof(f297,plain,
    ( spl7_39
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f292,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f289,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t1_subset)).

fof(f290,plain,
    ( ~ spl7_37
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f274,f250,f139,f288])).

fof(f139,plain,
    ( spl7_12
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f250,plain,
    ( spl7_32
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f274,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_12
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f140,f251,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t5_subset)).

fof(f251,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f250])).

fof(f140,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f269,plain,
    ( ~ spl7_35
    | ~ spl7_12
    | spl7_31 ),
    inference(avatar_split_clause,[],[f259,f241,f139,f267])).

fof(f267,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f241,plain,
    ( spl7_31
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f259,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f140,f242,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t8_boole)).

fof(f242,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f241])).

fof(f252,plain,
    ( spl7_30
    | spl7_32
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f230,f223,f139,f250,f244])).

fof(f244,plain,
    ( spl7_30
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f223,plain,
    ( spl7_28
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f230,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(resolution,[],[f187,f224])).

fof(f224,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f223])).

fof(f187,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl7_12 ),
    inference(resolution,[],[f85,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f156,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t6_boole)).

fof(f156,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f140,f74])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t2_subset)).

fof(f225,plain,
    ( spl7_28
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f218,f215,f223])).

fof(f215,plain,
    ( spl7_26
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f218,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_26 ),
    inference(superposition,[],[f82,f216])).

fof(f216,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f217,plain,
    ( spl7_26
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f202,f194,f139,f215])).

fof(f194,plain,
    ( spl7_24
  <=> v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f202,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f195,f158])).

fof(f195,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl7_24
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f189,f139,f194])).

fof(f189,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f82,f188,f85])).

fof(f188,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f140,f82,f89])).

fof(f184,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f71,f182])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ~ v5_pre_topc(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v5_pre_topc(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ v5_pre_topc(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',t68_tex_2)).

fof(f175,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f70,f173])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f165,plain,
    ( spl7_18
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f156,f139,f163])).

fof(f163,plain,
    ( spl7_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f155,plain,(
    ~ spl7_17 ),
    inference(avatar_split_clause,[],[f72,f153])).

fof(f72,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f148,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f92,f146])).

fof(f146,plain,
    ( spl7_14
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f92,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f62])).

fof(f62,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',existence_l1_pre_topc)).

fof(f141,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f73,f139])).

fof(f73,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t68_tex_2.p',dt_o_0_0_xboole_0)).

fof(f134,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f69,f132])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f127,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f68,f125])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f120,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f67,f118])).

fof(f118,plain,
    ( spl7_6
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f65,f104])).

fof(f65,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f64,f97])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
