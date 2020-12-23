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
% DateTime   : Thu Dec  3 13:22:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 980 expanded)
%              Number of leaves         :   37 ( 456 expanded)
%              Depth                    :   15
%              Number of atoms          :  688 (11288 expanded)
%              Number of equality atoms :  111 (2022 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f133,f137,f175,f203,f214,f220,f250,f257,f279,f290,f361])).

fof(f361,plain,
    ( ~ spl8_3
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f285,f246])).

fof(f246,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl8_22
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f285,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f104,f282])).

fof(f282,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f136,f123])).

fof(f123,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_3
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f136,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_6
  <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f104,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f71,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & v3_borsuk_1(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v5_pre_topc(sK2,sK0,sK1)
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & v4_tex_2(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                        & X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK0,X1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & v4_tex_2(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK0,X1)
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK0)
        & v4_tex_2(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK1)) )
          & v3_borsuk_1(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(X2,sK0,sK1)
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK1,sK0)
      & v4_tex_2(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK1)) )
        & v3_borsuk_1(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(X2,sK0,sK1)
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK1)) )
      & v3_borsuk_1(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v5_pre_topc(sK2,sK0,sK1)
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK1)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3))
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(f72,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f290,plain,
    ( ~ spl8_17
    | spl8_22
    | ~ spl8_16
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f289,f135,f131,f122,f201,f245,f207])).

fof(f207,plain,
    ( spl8_17
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f201,plain,
    ( spl8_16
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f131,plain,
    ( spl8_5
  <=> ! [X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f289,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(superposition,[],[f185,f283])).

fof(f283,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f262,f282])).

fof(f262,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f180,f136])).

fof(f180,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4)
    | ~ spl8_5 ),
    inference(resolution,[],[f132,f105])).

fof(f105,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f69,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f185,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k7_domain_1(u1_struct_0(sK1),X1,X2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_domain_1(u1_struct_0(sK1),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f161,f184])).

fof(f184,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k7_domain_1(u1_struct_0(sK1),X1,X2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_domain_1(u1_struct_0(sK1),X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f142,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ) ),
    inference(global_subsumption,[],[f57,f58,f59,f60,f61,f64,f62,f63,f66,f68,f65,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_borsuk_1(sK2,sK0,sK1)
      | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v4_tex_2(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v3_tdlat_3(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f161,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f57,f58,f60,f160,f155])).

fof(f155,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f111,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f60,f110])).

fof(f110,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f160,plain,(
    v3_tex_2(u1_struct_0(sK1),sK0) ),
    inference(global_subsumption,[],[f57,f60,f62,f63,f154])).

fof(f154,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK5(X0,X1),X0)
                & u1_struct_0(X1) = sK5(X0,X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK5(X0,X1),X0)
        & u1_struct_0(X1) = sK5(X0,X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f279,plain,(
    ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f161,f261])).

fof(f261,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_23 ),
    inference(resolution,[],[f256,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f256,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl8_23
  <=> ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f257,plain,
    ( ~ spl8_1
    | spl8_23 ),
    inference(avatar_split_clause,[],[f251,f255,f115])).

fof(f115,plain,
    ( spl8_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK1))
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f182,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f182,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f157,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f157,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f111,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f250,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f217,f122,f115])).

fof(f217,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f70,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f85,f103])).

fof(f103,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f102])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f84,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f91,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f94,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f95,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f96,f97])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f84,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f220,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl8_17 ),
    inference(subsumption_resolution,[],[f105,f208])).

fof(f208,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f207])).

fof(f214,plain,(
    spl8_15 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl8_15 ),
    inference(subsumption_resolution,[],[f70,f199])).

fof(f199,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl8_15
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f203,plain,
    ( spl8_1
    | ~ spl8_15
    | spl8_16
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f196,f122,f118,f201,f198,f115])).

fof(f118,plain,
    ( spl8_2
  <=> ! [X0] :
        ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f196,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(superposition,[],[f92,f179])).

fof(f179,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f178,f123])).

fof(f178,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4)
    | ~ spl8_2 ),
    inference(resolution,[],[f119,f70])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f175,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f129,f161])).

fof(f129,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_4
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f137,plain,
    ( spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f126,f135,f128])).

fof(f126,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f105,f106])).

fof(f133,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f125,f131,f128])).

fof(f125,plain,(
    ! [X0] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f105,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f93,f102])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f120,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f112,f118,f115])).

fof(f112,plain,(
    ! [X0] :
      ( k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f70,f107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21216)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (21216)Refutation not found, incomplete strategy% (21216)------------------------------
% 0.20/0.47  % (21216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21233)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.47  % (21216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (21216)Memory used [KB]: 6396
% 0.20/0.47  % (21216)Time elapsed: 0.053 s
% 0.20/0.47  % (21216)------------------------------
% 0.20/0.47  % (21216)------------------------------
% 0.20/0.54  % (21220)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (21214)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (21213)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.56  % (21240)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  % (21237)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (21221)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (21232)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (21236)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (21224)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (21229)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (21243)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.58  % (21224)Refutation not found, incomplete strategy% (21224)------------------------------
% 0.20/0.58  % (21224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (21224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (21224)Memory used [KB]: 10746
% 0.20/0.58  % (21224)Time elapsed: 0.141 s
% 0.20/0.58  % (21224)------------------------------
% 0.20/0.58  % (21224)------------------------------
% 0.20/0.58  % (21214)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f362,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f120,f133,f137,f175,f203,f214,f220,f250,f257,f279,f290,f361])).
% 0.20/0.58  fof(f361,plain,(
% 0.20/0.58    ~spl8_3 | ~spl8_6 | ~spl8_22),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f360])).
% 0.20/0.58  fof(f360,plain,(
% 0.20/0.58    $false | (~spl8_3 | ~spl8_6 | ~spl8_22)),
% 0.20/0.58    inference(subsumption_resolution,[],[f285,f246])).
% 0.20/0.58  fof(f246,plain,(
% 0.20/0.58    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~spl8_22),
% 0.20/0.58    inference(avatar_component_clause,[],[f245])).
% 0.20/0.58  fof(f245,plain,(
% 0.20/0.58    spl8_22 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.58  fof(f285,plain,(
% 0.20/0.58    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (~spl8_3 | ~spl8_6)),
% 0.20/0.58    inference(backward_demodulation,[],[f104,f282])).
% 0.20/0.58  fof(f282,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | (~spl8_3 | ~spl8_6)),
% 0.20/0.58    inference(backward_demodulation,[],[f136,f123])).
% 0.20/0.58  fof(f123,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f122])).
% 0.20/0.58  fof(f122,plain,(
% 0.20/0.58    spl8_3 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f135])).
% 0.20/0.58  fof(f135,plain,(
% 0.20/0.58    spl8_6 <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.20/0.58    inference(definition_unfolding,[],[f72,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    sK3 = sK4),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f42,f41,f40,f39,f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(X2,sK0,sK1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ? [X3] : (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(sK1))) => (? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ? [X4] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,negated_conjecture,(
% 0.20/0.58    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.58    inference(negated_conjecture,[],[f19])).
% 0.20/0.58  fof(f19,conjecture,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f290,plain,(
% 0.20/0.58    ~spl8_17 | spl8_22 | ~spl8_16 | ~spl8_3 | ~spl8_5 | ~spl8_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f289,f135,f131,f122,f201,f245,f207])).
% 0.20/0.58  fof(f207,plain,(
% 0.20/0.58    spl8_17 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.58  fof(f201,plain,(
% 0.20/0.58    spl8_16 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    spl8_5 <=> ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.58  fof(f289,plain,(
% 0.20/0.58    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f286])).
% 0.20/0.58  fof(f286,plain,(
% 0.20/0.58    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 0.20/0.58    inference(superposition,[],[f185,f283])).
% 0.20/0.58  fof(f283,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 0.20/0.58    inference(backward_demodulation,[],[f262,f282])).
% 0.20/0.58  fof(f262,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK1),sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | (~spl8_5 | ~spl8_6)),
% 0.20/0.58    inference(forward_demodulation,[],[f180,f136])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK1),sK4,sK4) | ~spl8_5),
% 0.20/0.58    inference(resolution,[],[f132,f105])).
% 0.20/0.58  fof(f105,plain,(
% 0.20/0.58    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.58    inference(definition_unfolding,[],[f69,f71])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f132,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4)) ) | ~spl8_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f131])).
% 0.20/0.58  fof(f185,plain,(
% 0.20/0.58    ( ! [X2,X1] : (~m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k7_domain_1(u1_struct_0(sK1),X1,X2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_domain_1(u1_struct_0(sK1),X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 0.20/0.58    inference(global_subsumption,[],[f161,f184])).
% 0.20/0.58  fof(f184,plain,(
% 0.20/0.58    ( ! [X2,X1] : (~m1_subset_1(k7_domain_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k7_domain_1(u1_struct_0(sK1),X1,X2)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_domain_1(u1_struct_0(sK1),X1,X2)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.58    inference(resolution,[],[f142,f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).
% 0.20/0.58  fof(f142,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) )),
% 0.20/0.58    inference(global_subsumption,[],[f57,f58,f59,f60,f61,f64,f62,f63,f66,f68,f65,f138])).
% 0.20/0.58  fof(f138,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_borsuk_1(sK2,sK0,sK1) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_pre_topc(sK1,sK0) | ~v4_tex_2(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.58    inference(resolution,[],[f67,f108])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    v3_borsuk_1(sK2,sK0,sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    m1_pre_topc(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    v4_tex_2(sK1,sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    v1_funct_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    ~v2_struct_0(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    l1_pre_topc(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    v3_tdlat_3(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    v2_pre_topc(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ~v2_struct_0(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f161,plain,(
% 0.20/0.58    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.58    inference(global_subsumption,[],[f57,f58,f60,f160,f155])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    ~v3_tex_2(u1_struct_0(sK1),sK0) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(resolution,[],[f111,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.58    inference(global_subsumption,[],[f60,f110])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.58    inference(resolution,[],[f63,f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    v3_tex_2(u1_struct_0(sK1),sK0)),
% 0.20/0.58    inference(global_subsumption,[],[f57,f60,f62,f63,f154])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    v3_tex_2(u1_struct_0(sK1),sK0) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.58    inference(resolution,[],[f111,f109])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(u1_struct_0(X1),X0) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK5(X0,X1),X0) & u1_struct_0(X1) = sK5(X0,X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK5(X0,X1),X0) & u1_struct_0(X1) = sK5(X0,X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(rectify,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.20/0.58  fof(f279,plain,(
% 0.20/0.58    ~spl8_23),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f278])).
% 0.20/0.58  fof(f278,plain,(
% 0.20/0.58    $false | ~spl8_23),
% 0.20/0.58    inference(subsumption_resolution,[],[f161,f261])).
% 0.20/0.58  fof(f261,plain,(
% 0.20/0.58    v1_xboole_0(u1_struct_0(sK1)) | ~spl8_23),
% 0.20/0.58    inference(resolution,[],[f256,f83])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f49,f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(rectify,[],[f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.58  fof(f256,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1))) ) | ~spl8_23),
% 0.20/0.58    inference(avatar_component_clause,[],[f255])).
% 0.20/0.58  fof(f255,plain,(
% 0.20/0.58    spl8_23 <=> ! [X0] : ~r2_hidden(X0,u1_struct_0(sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.58  fof(f257,plain,(
% 0.20/0.58    ~spl8_1 | spl8_23),
% 0.20/0.58    inference(avatar_split_clause,[],[f251,f255,f115])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    spl8_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.58  fof(f251,plain,(
% 0.20/0.58    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 0.20/0.58    inference(resolution,[],[f182,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f51])).
% 0.20/0.58  fof(f182,plain,(
% 0.20/0.58    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK1))) )),
% 0.20/0.58    inference(resolution,[],[f157,f86])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f53,f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(rectify,[],[f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.58    inference(nnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.58    inference(resolution,[],[f111,f89])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.58  fof(f250,plain,(
% 0.20/0.58    spl8_1 | spl8_3),
% 0.20/0.58    inference(avatar_split_clause,[],[f217,f122,f115])).
% 0.20/0.58  fof(f217,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.58    inference(resolution,[],[f70,f106])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f85,f103])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f73,f102])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f84,f101])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f91,f100])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f94,f99])).
% 0.20/0.58  fof(f99,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f95,f98])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f96,f97])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f31])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f220,plain,(
% 0.20/0.58    spl8_17),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.58  fof(f219,plain,(
% 0.20/0.58    $false | spl8_17),
% 0.20/0.58    inference(subsumption_resolution,[],[f105,f208])).
% 0.20/0.58  fof(f208,plain,(
% 0.20/0.58    ~m1_subset_1(sK4,u1_struct_0(sK1)) | spl8_17),
% 0.20/0.58    inference(avatar_component_clause,[],[f207])).
% 0.20/0.58  fof(f214,plain,(
% 0.20/0.58    spl8_15),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.58  fof(f213,plain,(
% 0.20/0.58    $false | spl8_15),
% 0.20/0.58    inference(subsumption_resolution,[],[f70,f199])).
% 0.20/0.58  fof(f199,plain,(
% 0.20/0.58    ~m1_subset_1(sK4,u1_struct_0(sK0)) | spl8_15),
% 0.20/0.58    inference(avatar_component_clause,[],[f198])).
% 0.20/0.58  fof(f198,plain,(
% 0.20/0.58    spl8_15 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.58  fof(f203,plain,(
% 0.20/0.58    spl8_1 | ~spl8_15 | spl8_16 | ~spl8_2 | ~spl8_3),
% 0.20/0.58    inference(avatar_split_clause,[],[f196,f122,f118,f201,f198,f115])).
% 0.20/0.58  fof(f118,plain,(
% 0.20/0.58    spl8_2 <=> ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.58  fof(f196,plain,(
% 0.20/0.58    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl8_2 | ~spl8_3)),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f195])).
% 0.20/0.58  fof(f195,plain,(
% 0.20/0.58    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | ~m1_subset_1(sK4,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl8_2 | ~spl8_3)),
% 0.20/0.58    inference(superposition,[],[f92,f179])).
% 0.20/0.58  fof(f179,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK0),sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | (~spl8_2 | ~spl8_3)),
% 0.20/0.58    inference(forward_demodulation,[],[f178,f123])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k7_domain_1(u1_struct_0(sK0),sK4,sK4) | ~spl8_2),
% 0.20/0.58    inference(resolution,[],[f119,f70])).
% 0.20/0.58  fof(f119,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) ) | ~spl8_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f118])).
% 0.20/0.58  fof(f175,plain,(
% 0.20/0.58    ~spl8_4),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.58  fof(f174,plain,(
% 0.20/0.58    $false | ~spl8_4),
% 0.20/0.58    inference(subsumption_resolution,[],[f129,f161])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    v1_xboole_0(u1_struct_0(sK1)) | ~spl8_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f128])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    spl8_4 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.58  fof(f137,plain,(
% 0.20/0.58    spl8_4 | spl8_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f126,f135,f128])).
% 0.20/0.58  fof(f126,plain,(
% 0.20/0.58    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.58    inference(resolution,[],[f105,f106])).
% 0.20/0.58  fof(f133,plain,(
% 0.20/0.58    spl8_4 | spl8_5),
% 0.20/0.58    inference(avatar_split_clause,[],[f125,f131,f128])).
% 0.20/0.58  fof(f125,plain,(
% 0.20/0.58    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) = k7_domain_1(u1_struct_0(sK1),X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))) )),
% 0.20/0.58    inference(resolution,[],[f105,f107])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f93,f102])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    spl8_1 | spl8_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f112,f118,f115])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ( ! [X0] : (k7_domain_1(u1_struct_0(sK0),X0,sK4) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.20/0.58    inference(resolution,[],[f70,f107])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (21214)------------------------------
% 0.20/0.58  % (21214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (21214)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (21214)Memory used [KB]: 11001
% 0.20/0.58  % (21214)Time elapsed: 0.140 s
% 0.20/0.58  % (21214)------------------------------
% 0.20/0.58  % (21214)------------------------------
% 1.57/0.59  % (21209)Success in time 0.229 s
%------------------------------------------------------------------------------
