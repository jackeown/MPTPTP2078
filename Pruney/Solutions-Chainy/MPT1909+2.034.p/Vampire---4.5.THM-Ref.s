%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 752 expanded)
%              Number of leaves         :   19 ( 331 expanded)
%              Depth                    :   33
%              Number of atoms          :  685 (9094 expanded)
%              Number of equality atoms :   79 (1542 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f209,f295,f88])).

fof(f88,plain,
    ( ~ sP8(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP8(X1) ) ),
    inference(general_splitting,[],[f73,f79_D])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP8(X1) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP8(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f82,plain,
    ( r2_hidden(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f70,f75])).

fof(f75,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f13,f35,f34,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5))
        & sK5 = X4
        & m1_subset_1(X4,u1_struct_0(sK2)) )
   => ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

fof(f55,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f295,plain,(
    sP8(u1_struct_0(sK3)) ),
    inference(resolution,[],[f294,f133])).

fof(f133,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | sP8(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f132,f46])).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | sP8(u1_struct_0(sK3)) ),
    inference(resolution,[],[f99,f49])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | sP8(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f60,f79])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f294,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f293,f56])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f293,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f276,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f72,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f59])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f276,plain,
    ( ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f275,f209])).

fof(f275,plain,
    ( ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f274,f75])).

fof(f274,plain,
    ( ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f273,f105])).

fof(f273,plain,
    ( ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f270,f56])).

fof(f270,plain,
    ( ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( k2_pre_topc(sK2,k2_tarski(sK6,sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f266,f76])).

fof(f266,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f190,f209])).

fof(f190,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f189,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f188,f44])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f188,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f187,f45])).

fof(f45,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f187,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f186,f46])).

fof(f186,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f185,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f185,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f184,f48])).

fof(f48,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f184,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f183,f49])).

fof(f183,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f182,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f182,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f181,f51])).

fof(f51,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f181,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f52,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f180,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(subsumption_resolution,[],[f179,f53])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f179,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(subsumption_resolution,[],[f178,f54])).

fof(f54,plain,(
    v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f178,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))
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
    inference(superposition,[],[f112,f77])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

fof(f112,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f111,f75])).

fof(f111,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f74,f76])).

fof(f74,plain,(
    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f58,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f36])).

fof(f209,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f208,f49])).

fof(f208,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f207,f43])).

fof(f207,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f206,f44])).

fof(f206,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f205,f46])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f148,f98])).

fof(f98,plain,(
    sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f97,f48])).

fof(f97,plain,
    ( ~ v4_tex_2(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v4_tex_2(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_tex_2(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_tex_2(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( ( v4_tex_2(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v4_tex_2(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( v4_tex_2(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f95,plain,(
    sP1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f94,plain,
    ( sP1(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,
    ( sP1(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f69,f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sP1(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f20,f29,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( v3_tex_2(X2,X0)
          | u1_struct_0(X1) != X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ sP0(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ sP0(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f110,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X0),X1)
      | ~ sP0(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK7(X0,X1),X0)
        & u1_struct_0(X1) = sK7(X0,X1)
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ v3_tex_2(u1_struct_0(X2),X3)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X3] :
      ( ~ v3_tex_2(u1_struct_0(X2),X3)
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f62,f60])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (20724)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (20748)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (20731)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (20718)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (20748)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (20727)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (20728)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (20723)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f209,f295,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ~sP8(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f82,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP8(X1)) )),
% 0.20/0.52    inference(general_splitting,[],[f73,f79_D])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP8(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f79_D])).
% 0.20/0.52  fof(f79_D,plain,(
% 0.20/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP8(X1)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    r2_hidden(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f70,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.52    inference(definition_unfolding,[],[f55,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    sK5 = sK6),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ((((k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f13,f35,f34,f33,f32,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X2] : (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ? [X3] : (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),X3)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(sK3))) => (? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ? [X4] : (k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) => (k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    sP8(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f294,f133])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ~v1_xboole_0(u1_struct_0(sK2)) | sP8(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    l1_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ~l1_pre_topc(sK2) | ~v1_xboole_0(u1_struct_0(sK2)) | sP8(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f99,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    m1_pre_topc(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v1_xboole_0(u1_struct_0(X1)) | sP8(u1_struct_0(X0))) )),
% 0.20/0.52    inference(resolution,[],[f60,f79])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f293,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f293,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f292])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f276,f105])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(superposition,[],[f72,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f71,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.52  fof(f276,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f275,f209])).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f274,f75])).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f273,f105])).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f270,f56])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f269])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k2_tarski(sK6,sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(superposition,[],[f266,f76])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f190,f209])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ~v2_struct_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f188,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v2_pre_topc(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f187,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v3_tdlat_3(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f186,f46])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f185,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ~v2_struct_0(sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f184,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    v4_tex_2(sK3,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f183,f49])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f182,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v1_funct_1(sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f181,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    v5_pre_topc(sK4,sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f179,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f178,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    v3_borsuk_1(sK4,sK2,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_borsuk_1(sK4,sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK2) | ~v4_tex_2(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v3_tdlat_3(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(superposition,[],[f112,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f111,f75])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(superposition,[],[f74,f76])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6))),
% 0.20/0.52    inference(definition_unfolding,[],[f58,f57])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f208,f49])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f207,f43])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f206,f44])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(subsumption_resolution,[],[f205,f46])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK2) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.20/0.52    inference(resolution,[],[f148,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    sP0(sK2,sK3)),
% 0.20/0.52    inference(subsumption_resolution,[],[f97,f48])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ~v4_tex_2(sK3,sK2) | sP0(sK2,sK3)),
% 0.20/0.52    inference(resolution,[],[f95,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | ~v4_tex_2(X0,X1) | sP0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : (((v4_tex_2(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_tex_2(X0,X1))) | ~sP1(X0,X1))),
% 0.20/0.52    inference(rectify,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X1,X0] : (((v4_tex_2(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v4_tex_2(X1,X0))) | ~sP1(X1,X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X1,X0] : ((v4_tex_2(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    sP1(sK3,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f94,f43])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    sP1(sK3,sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f93,f46])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    sP1(sK3,sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f69,f49])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | sP1(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(definition_folding,[],[f20,f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP0(X1,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~sP0(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.52    inference(resolution,[],[f110,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X0),X1) | ~sP0(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.52    inference(resolution,[],[f78,f60])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(u1_struct_0(X1),X0) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | (~v3_tex_2(sK7(X0,X1),X0) & u1_struct_0(X1) = sK7(X0,X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f40,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK7(X0,X1),X0) & u1_struct_0(X1) = sK7(X0,X1) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f28])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~v3_tex_2(u1_struct_0(X2),X3) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f108])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~v3_tex_2(u1_struct_0(X2),X3) | ~v1_xboole_0(u1_struct_0(X2)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 0.20/0.52    inference(resolution,[],[f62,f60])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20748)------------------------------
% 0.20/0.52  % (20748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20748)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (20748)Memory used [KB]: 1918
% 0.20/0.52  % (20748)Time elapsed: 0.103 s
% 0.20/0.52  % (20748)------------------------------
% 0.20/0.52  % (20748)------------------------------
% 0.20/0.52  % (20717)Success in time 0.169 s
%------------------------------------------------------------------------------
