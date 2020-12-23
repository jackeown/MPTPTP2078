%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1909+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 49.68s
% Output     : Refutation 49.68s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 720 expanded)
%              Number of leaves         :   16 ( 319 expanded)
%              Depth                    :   27
%              Number of atoms          :  505 (8532 expanded)
%              Number of equality atoms :   73 (1494 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106199,plain,(
    $false ),
    inference(subsumption_resolution,[],[f106198,f106189])).

fof(f106189,plain,(
    m1_subset_1(k2_tarski(sK116,sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(subsumption_resolution,[],[f106164,f19093])).

fof(f19093,plain,(
    ~ v1_xboole_0(u1_struct_0(sK113)) ),
    inference(backward_demodulation,[],[f19065,f19033])).

fof(f19033,plain,(
    u1_struct_0(sK113) = k2_struct_0(sK113) ),
    inference(resolution,[],[f16210,f7027])).

fof(f7027,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4268])).

fof(f4268,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f16210,plain,(
    l1_struct_0(sK113) ),
    inference(resolution,[],[f12464,f7033])).

fof(f7033,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4275])).

fof(f4275,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f12464,plain,(
    l1_pre_topc(sK113) ),
    inference(subsumption_resolution,[],[f12128,f6350])).

fof(f6350,plain,(
    l1_pre_topc(sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f5341,plain,
    ( k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK115)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),sK116))
    & sK115 = sK116
    & m1_subset_1(sK116,u1_struct_0(sK112))
    & m1_subset_1(sK115,u1_struct_0(sK113))
    & v3_borsuk_1(sK114,sK112,sK113)
    & m1_subset_1(sK114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
    & v5_pre_topc(sK114,sK112,sK113)
    & v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
    & v1_funct_1(sK114)
    & m1_pre_topc(sK113,sK112)
    & v4_tex_2(sK113,sK112)
    & ~ v2_struct_0(sK113)
    & l1_pre_topc(sK112)
    & v3_tdlat_3(sK112)
    & v2_pre_topc(sK112)
    & ~ v2_struct_0(sK112) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK112,sK113,sK114,sK115,sK116])],[f3794,f5340,f5339,f5338,f5337,f5336])).

fof(f5336,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3))
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
                      ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK112)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK112,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK112,X1)
              & v1_funct_2(X2,u1_struct_0(sK112),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK112)
          & v4_tex_2(X1,sK112)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK112)
      & v3_tdlat_3(sK112)
      & v2_pre_topc(sK112)
      & ~ v2_struct_0(sK112) ) ),
    introduced(choice_axiom,[])).

fof(f5337,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK112)) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & v3_borsuk_1(X2,sK112,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(X1))))
            & v5_pre_topc(X2,sK112,X1)
            & v1_funct_2(X2,u1_struct_0(sK112),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & m1_pre_topc(X1,sK112)
        & v4_tex_2(X1,sK112)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),X2,k6_domain_1(u1_struct_0(sK113),X3))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK112)) )
              & m1_subset_1(X3,u1_struct_0(sK113)) )
          & v3_borsuk_1(X2,sK112,sK113)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
          & v5_pre_topc(X2,sK112,sK113)
          & v1_funct_2(X2,u1_struct_0(sK112),u1_struct_0(sK113))
          & v1_funct_1(X2) )
      & m1_pre_topc(sK113,sK112)
      & v4_tex_2(sK113,sK112)
      & ~ v2_struct_0(sK113) ) ),
    introduced(choice_axiom,[])).

fof(f5338,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),X2,k6_domain_1(u1_struct_0(sK113),X3))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK112)) )
            & m1_subset_1(X3,u1_struct_0(sK113)) )
        & v3_borsuk_1(X2,sK112,sK113)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
        & v5_pre_topc(X2,sK112,sK113)
        & v1_funct_2(X2,u1_struct_0(sK112),u1_struct_0(sK113))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),X3))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK112)) )
          & m1_subset_1(X3,u1_struct_0(sK113)) )
      & v3_borsuk_1(sK114,sK112,sK113)
      & m1_subset_1(sK114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
      & v5_pre_topc(sK114,sK112,sK113)
      & v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
      & v1_funct_1(sK114) ) ),
    introduced(choice_axiom,[])).

fof(f5339,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),X3))
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK112)) )
        & m1_subset_1(X3,u1_struct_0(sK113)) )
   => ( ? [X4] :
          ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK115))
          & sK115 = X4
          & m1_subset_1(X4,u1_struct_0(sK112)) )
      & m1_subset_1(sK115,u1_struct_0(sK113)) ) ),
    introduced(choice_axiom,[])).

fof(f5340,plain,
    ( ? [X4] :
        ( k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),X4)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK115))
        & sK115 = X4
        & m1_subset_1(X4,u1_struct_0(sK112)) )
   => ( k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK115)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),sK116))
      & sK115 = sK116
      & m1_subset_1(sK116,u1_struct_0(sK112)) ) ),
    introduced(choice_axiom,[])).

fof(f3794,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3))
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
    inference(flattening,[],[f3793])).

fof(f3793,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3))
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
    inference(ennf_transformation,[],[f3769])).

fof(f3769,negated_conjecture,(
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
                           => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3768])).

fof(f3768,conjecture,(
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
                         => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(f12128,plain,
    ( l1_pre_topc(sK113)
    | ~ l1_pre_topc(sK112) ),
    inference(resolution,[],[f6353,f6509])).

fof(f6509,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3906])).

fof(f3906,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f6353,plain,(
    m1_pre_topc(sK113,sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f19065,plain,(
    ~ v1_xboole_0(k2_struct_0(sK113)) ),
    inference(subsumption_resolution,[],[f19031,f6351])).

fof(f6351,plain,(
    ~ v2_struct_0(sK113) ),
    inference(cnf_transformation,[],[f5341])).

fof(f19031,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK113))
    | v2_struct_0(sK113) ),
    inference(resolution,[],[f16210,f7003])).

fof(f7003,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4260])).

fof(f4260,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4259])).

fof(f4259,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1800])).

fof(f1800,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f106164,plain,
    ( m1_subset_1(k2_tarski(sK116,sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | v1_xboole_0(u1_struct_0(sK113)) ),
    inference(backward_demodulation,[],[f13575,f106123])).

fof(f106123,plain,(
    k6_domain_1(u1_struct_0(sK113),sK116) = k2_tarski(sK116,sK116) ),
    inference(resolution,[],[f13598,f19093])).

fof(f13598,plain,
    ( v1_xboole_0(u1_struct_0(sK113))
    | k6_domain_1(u1_struct_0(sK113),sK116) = k2_tarski(sK116,sK116) ),
    inference(resolution,[],[f8522,f8525])).

fof(f8525,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f6459,f8519])).

fof(f8519,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f6459,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3863])).

fof(f3863,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3862])).

fof(f3862,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f8522,plain,(
    m1_subset_1(sK116,u1_struct_0(sK113)) ),
    inference(definition_unfolding,[],[f6359,f6361])).

fof(f6361,plain,(
    sK115 = sK116 ),
    inference(cnf_transformation,[],[f5341])).

fof(f6359,plain,(
    m1_subset_1(sK115,u1_struct_0(sK113)) ),
    inference(cnf_transformation,[],[f5341])).

fof(f13575,plain,
    ( v1_xboole_0(u1_struct_0(sK113))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(resolution,[],[f8522,f6458])).

fof(f6458,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3861])).

fof(f3861,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3860])).

fof(f3860,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1893])).

fof(f1893,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f106198,plain,(
    ~ m1_subset_1(k2_tarski(sK116,sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(forward_demodulation,[],[f106188,f106123])).

fof(f106188,plain,(
    ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(trivial_inequality_removal,[],[f106176])).

fof(f106176,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k2_tarski(sK116,sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(backward_demodulation,[],[f16017,f106123])).

fof(f16017,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(subsumption_resolution,[],[f16016,f12461])).

fof(f12461,plain,(
    ! [X41] :
      ( m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK112)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK113))) ) ),
    inference(subsumption_resolution,[],[f12124,f6350])).

fof(f12124,plain,(
    ! [X41] :
      ( m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK112)))
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(sK113)))
      | ~ l1_pre_topc(sK112) ) ),
    inference(resolution,[],[f6353,f6505])).

fof(f6505,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3902])).

fof(f3902,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1832])).

fof(f1832,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f16016,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113))) ),
    inference(subsumption_resolution,[],[f16015,f6347])).

fof(f6347,plain,(
    ~ v2_struct_0(sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16015,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16014,f6348])).

fof(f6348,plain,(
    v2_pre_topc(sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16014,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16013,f6349])).

fof(f6349,plain,(
    v3_tdlat_3(sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16013,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16012,f6350])).

fof(f16012,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16011,f6351])).

fof(f16011,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16010,f6352])).

fof(f6352,plain,(
    v4_tex_2(sK113,sK112) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16010,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16009,f6353])).

fof(f16009,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16008,f6354])).

fof(f6354,plain,(
    v1_funct_1(sK114) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16008,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v1_funct_1(sK114)
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16007,f6355])).

fof(f6355,plain,(
    v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113)) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16007,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
    | ~ v1_funct_1(sK114)
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16006,f6356])).

fof(f6356,plain,(
    v5_pre_topc(sK114,sK112,sK113) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16006,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v5_pre_topc(sK114,sK112,sK113)
    | ~ v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
    | ~ v1_funct_1(sK114)
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f16005,f6357])).

fof(f6357,plain,(
    m1_subset_1(sK114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113)))) ),
    inference(cnf_transformation,[],[f5341])).

fof(f16005,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ m1_subset_1(sK114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
    | ~ v5_pre_topc(sK114,sK112,sK113)
    | ~ v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
    | ~ v1_funct_1(sK114)
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(subsumption_resolution,[],[f15999,f6358])).

fof(f6358,plain,(
    v3_borsuk_1(sK114,sK112,sK113) ),
    inference(cnf_transformation,[],[f5341])).

fof(f15999,plain,
    ( k2_pre_topc(sK112,k2_tarski(sK116,sK116)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK113),sK116))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK112)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK113),sK116),k1_zfmisc_1(u1_struct_0(sK113)))
    | ~ v3_borsuk_1(sK114,sK112,sK113)
    | ~ m1_subset_1(sK114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK112),u1_struct_0(sK113))))
    | ~ v5_pre_topc(sK114,sK112,sK113)
    | ~ v1_funct_2(sK114,u1_struct_0(sK112),u1_struct_0(sK113))
    | ~ v1_funct_1(sK114)
    | ~ m1_pre_topc(sK113,sK112)
    | ~ v4_tex_2(sK113,sK112)
    | v2_struct_0(sK113)
    | ~ l1_pre_topc(sK112)
    | ~ v3_tdlat_3(sK112)
    | ~ v2_pre_topc(sK112)
    | v2_struct_0(sK112) ),
    inference(superposition,[],[f13527,f8790])).

fof(f8790,plain,(
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
    inference(equality_resolution,[],[f6481])).

fof(f6481,plain,(
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
    inference(cnf_transformation,[],[f3877])).

fof(f3877,plain,(
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
    inference(flattening,[],[f3876])).

fof(f3876,plain,(
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
    inference(ennf_transformation,[],[f3767])).

fof(f3767,axiom,(
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

fof(f13527,plain,(
    k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK116)) != k2_pre_topc(sK112,k2_tarski(sK116,sK116)) ),
    inference(backward_demodulation,[],[f8521,f13526])).

fof(f13526,plain,(
    k6_domain_1(u1_struct_0(sK112),sK116) = k2_tarski(sK116,sK116) ),
    inference(subsumption_resolution,[],[f13444,f13520])).

fof(f13520,plain,(
    ~ v1_xboole_0(u1_struct_0(sK112)) ),
    inference(global_subsumption,[],[f9103,f10644])).

fof(f10644,plain,(
    l1_struct_0(sK112) ),
    inference(resolution,[],[f6350,f7033])).

fof(f9103,plain,
    ( ~ l1_struct_0(sK112)
    | ~ v1_xboole_0(u1_struct_0(sK112)) ),
    inference(resolution,[],[f6347,f7032])).

fof(f7032,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4274])).

fof(f4274,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4273])).

fof(f4273,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f13444,plain,
    ( k6_domain_1(u1_struct_0(sK112),sK116) = k2_tarski(sK116,sK116)
    | v1_xboole_0(u1_struct_0(sK112)) ),
    inference(resolution,[],[f6360,f8525])).

fof(f6360,plain,(
    m1_subset_1(sK116,u1_struct_0(sK112)) ),
    inference(cnf_transformation,[],[f5341])).

fof(f8521,plain,(
    k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),sK116)) != k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK116)) ),
    inference(definition_unfolding,[],[f6362,f6361])).

fof(f6362,plain,(
    k8_relset_1(u1_struct_0(sK112),u1_struct_0(sK113),sK114,k6_domain_1(u1_struct_0(sK113),sK115)) != k2_pre_topc(sK112,k6_domain_1(u1_struct_0(sK112),sK116)) ),
    inference(cnf_transformation,[],[f5341])).
%------------------------------------------------------------------------------
