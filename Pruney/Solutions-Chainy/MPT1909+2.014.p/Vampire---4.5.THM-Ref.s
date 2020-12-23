%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 786 expanded)
%              Number of leaves         :   25 ( 339 expanded)
%              Depth                    :   30
%              Number of atoms          :  723 (8806 expanded)
%              Number of equality atoms :  105 (1553 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f224,f399,f138])).

fof(f138,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f137,f54])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v3_borsuk_1(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v5_pre_topc(sK4,sK2,sK3)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & v4_tex_2(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f43,f42,f41,f40,f39])).

fof(f39,plain,
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
                      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK2,X1)
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & v4_tex_2(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK2,X1)
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK2)
        & v4_tex_2(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK2)) )
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & v3_borsuk_1(X2,sK2,sK3)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(X2,sK2,sK3)
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK3,sK2)
      & v4_tex_2(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK2)) )
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & v3_borsuk_1(X2,sK2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(X2,sK2,sK3)
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK2)) )
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & v3_borsuk_1(sK4,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v5_pre_topc(sK4,sK2,sK3)
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK2)) )
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5))
          & sK5 = X4
          & m1_subset_1(X4,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5))
        & sK5 = X4
        & m1_subset_1(X4,u1_struct_0(sK2)) )
   => ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f137,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f113,f57])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f68,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f399,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f398,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f398,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f397,f224])).

fof(f397,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f396,f96])).

fof(f96,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f65,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f396,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f388,f208])).

fof(f208,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k6_domain_1(X5,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k6_domain_1(X5,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,X3)
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3) ) ),
    inference(superposition,[],[f83,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X2,X0) = k7_domain_1(X1,X0,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X2,X0) = k7_domain_1(X1,X0,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f97,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f82,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f85,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f86,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f87,f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f80,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f81,f94])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f93])).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f388,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f380,f64])).

fof(f380,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f237])).

fof(f237,plain,(
    ! [X1] :
      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6))
      | ~ m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f236,f224])).

fof(f236,plain,(
    ! [X1] :
      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6))
      | ~ m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f232,f96])).

fof(f232,plain,(
    ! [X1] :
      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6))
      | ~ m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(sK6,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f152,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k6_domain_1(X1,X0) = k6_domain_1(X2,X0)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f97,f97])).

fof(f152,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f151,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f150,f52])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f150,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f149,f53])).

fof(f53,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f148,f54])).

fof(f148,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f147,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f147,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f56,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f146,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f145,f57])).

fof(f145,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f144,f58])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f144,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f143,f59])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f143,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f142,f60])).

fof(f60,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f141,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f62,plain,(
    v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_borsuk_1(sK4,sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f95,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(subsumption_resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f95,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f44])).

fof(f224,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f223,f57])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f222,f51])).

fof(f222,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f221,f52])).

fof(f221,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f220,f54])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f173,f112])).

fof(f112,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f111,f56])).

fof(f111,plain,
    ( ~ v4_tex_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f109,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v4_tex_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( ( v4_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v4_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( v4_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f109,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f108,f51])).

fof(f108,plain,
    ( sP1(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f107,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f79,f57])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v3_tex_2(X2,X0)
          | u1_struct_0(X1) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ sP0(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f126,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X0),X1)
      | ~ sP0(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f100,f68])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v3_tex_2(sK7(X0,X1),X0)
          & u1_struct_0(X1) = sK7(X0,X1)
          & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_tex_2(X3,X0)
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK7(X0,X1),X0)
        & u1_struct_0(X1) = sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_tex_2(X2,X0)
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v3_tex_2(X3,X0)
            | u1_struct_0(X1) != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v3_tex_2(X2,X0)
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( v3_tex_2(X2,X0)
            | u1_struct_0(X1) != X2
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ v3_tex_2(u1_struct_0(X2),X3)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ v3_tex_2(u1_struct_0(X2),X3)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f72,f68])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (31056)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.48  % (31045)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (31056)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f224,f399,f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    l1_pre_topc(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ((((k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f20,f43,f42,f41,f40,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) => (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) => (k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f17])).
% 0.21/0.50  fof(f17,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | v1_xboole_0(u1_struct_0(sK3)) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f113,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    m1_pre_topc(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(u1_struct_0(X1))) )),
% 0.21/0.50    inference(resolution,[],[f68,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f398,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f397,f224])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f396,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.50    inference(definition_unfolding,[],[f63,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    sK5 = sK6),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f389])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f388,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (m1_subset_1(k6_domain_1(X5,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,X5) | v1_xboole_0(X5)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f207])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (m1_subset_1(k6_domain_1(X5,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X4,X3) | ~m1_subset_1(X4,X3) | v1_xboole_0(X3) | ~m1_subset_1(X4,X5) | v1_xboole_0(X5) | ~m1_subset_1(X4,X3) | v1_xboole_0(X3)) )),
% 0.21/0.50    inference(superposition,[],[f83,f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k6_domain_1(X2,X0) = k7_domain_1(X1,X0,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k6_domain_1(X2,X0) = k7_domain_1(X1,X0,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(superposition,[],[f97,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f84,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f80,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f82,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f85,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f86,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f87,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f81,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f67,f93])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f380,f64])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    ~m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.50    inference(equality_resolution,[],[f237])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ( ! [X1] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6)) | ~m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f224])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ( ! [X1] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6)) | ~m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK6,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f232,f96])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X1] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(X1,sK6)) | ~m1_subset_1(k6_domain_1(X1,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK6,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(superposition,[],[f152,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k6_domain_1(X1,X0) = k6_domain_1(X2,X0) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(superposition,[],[f97,f97])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    v2_pre_topc(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v3_tdlat_3(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f54])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v2_struct_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f146,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v4_tex_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f145,f57])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v5_pre_topc(sK4,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f141,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f140,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    v3_borsuk_1(sK4,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_borsuk_1(sK4,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(superposition,[],[f95,f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f99,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6))),
% 0.21/0.50    inference(definition_unfolding,[],[f66,f65])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 0.21/0.50    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f223,f57])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f222,f51])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f52])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    inference(subsumption_resolution,[],[f220,f54])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.51    inference(resolution,[],[f173,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    sP0(sK2,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f56])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~v4_tex_2(sK3,sK2) | sP0(sK2,sK3)),
% 0.21/0.51    inference(resolution,[],[f109,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP1(X0,X1) | ~v4_tex_2(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : (((v4_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.21/0.51    inference(rectify,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X1,X0] : (((v4_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v4_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0] : ((v4_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    sP1(sK3,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f51])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    sP1(sK3,sK2) | v2_struct_0(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f107,f54])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    sP1(sK3,sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f79,f57])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP1(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(definition_folding,[],[f29,f37,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP0(X1,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~sP0(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.51    inference(resolution,[],[f126,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X0),X1) | ~sP0(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.51    inference(resolution,[],[f100,f68])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(u1_struct_0(X1),X0) | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | (~v3_tex_2(sK7(X0,X1),X0) & u1_struct_0(X1) = sK7(X0,X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f48,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK7(X0,X1),X0) & u1_struct_0(X1) = sK7(X0,X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f36])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v3_tex_2(u1_struct_0(X2),X3) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v3_tex_2(u1_struct_0(X2),X3) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 0.21/0.51    inference(resolution,[],[f72,f68])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31056)------------------------------
% 0.21/0.52  % (31056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31056)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31056)Memory used [KB]: 1918
% 0.21/0.52  % (31056)Time elapsed: 0.075 s
% 0.21/0.52  % (31056)------------------------------
% 0.21/0.52  % (31056)------------------------------
% 0.21/0.52  % (31024)Success in time 0.156 s
%------------------------------------------------------------------------------
