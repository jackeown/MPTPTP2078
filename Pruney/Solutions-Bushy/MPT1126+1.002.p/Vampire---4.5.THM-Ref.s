%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1126+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  138 (1953 expanded)
%              Number of leaves         :   24 ( 808 expanded)
%              Depth                    :   20
%              Number of atoms          :  524 (23798 expanded)
%              Number of equality atoms :   79 (2257 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(subsumption_resolution,[],[f629,f165])).

fof(f165,plain,(
    ~ v4_pre_topc(k10_relat_1(sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(forward_demodulation,[],[f152,f153])).

fof(f153,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f91,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f65,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ v5_pre_topc(sK4,sK0,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & v5_pre_topc(sK2,sK0,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f23,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ v5_pre_topc(X4,X0,X3)
                        & X2 = X4
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                        & v1_funct_1(X4) )
                    & v5_pre_topc(X2,X0,X1)
                    & m1_pre_topc(X3,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,sK0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,sK0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ v5_pre_topc(X4,sK0,X3)
                    & X2 = X4
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                & v5_pre_topc(X2,sK0,X1)
                & m1_pre_topc(X3,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v5_pre_topc(X4,sK0,X3)
                  & X2 = X4
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                  & v1_funct_1(X4) )
              & v5_pre_topc(X2,sK0,sK1)
              & m1_pre_topc(X3,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ v5_pre_topc(X4,sK0,X3)
                & X2 = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & v5_pre_topc(X2,sK0,sK1)
            & m1_pre_topc(X3,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ v5_pre_topc(X4,sK0,X3)
              & sK2 = X4
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & v5_pre_topc(sK2,sK0,sK1)
          & m1_pre_topc(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ v5_pre_topc(X4,sK0,X3)
            & sK2 = X4
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
            & v1_funct_1(X4) )
        & v5_pre_topc(sK2,sK0,sK1)
        & m1_pre_topc(X3,sK1) )
   => ( ? [X4] :
          ( ~ v5_pre_topc(X4,sK0,sK3)
          & sK2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & v5_pre_topc(sK2,sK0,sK1)
      & m1_pre_topc(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ~ v5_pre_topc(X4,sK0,sK3)
        & sK2 = X4
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ~ v5_pre_topc(sK4,sK0,sK3)
      & sK2 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,X0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v5_pre_topc(X4,X0,X3)
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                      & v1_funct_1(X4) )
                  & v5_pre_topc(X2,X0,X1)
                  & m1_pre_topc(X3,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_pre_topc(X3,X1)
                   => ( v5_pre_topc(X2,X0,X1)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( X2 = X4
                           => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

% (17293)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_pre_topc(X3,X1)
                   => ( v5_pre_topc(X2,X0,X1)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( X2 = X4
                           => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_pre_topc(X3,X1)
                   => ( v5_pre_topc(X2,X0,X1)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( X2 = X4
                           => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X1)
                 => ( v5_pre_topc(X2,X0,X1)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          & v1_funct_1(X4) )
                       => ( X2 = X4
                         => v5_pre_topc(X4,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_pre_topc)).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f152,plain,(
    ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f110,f93,f90,f92,f91,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
                    & v4_pre_topc(sK5(X0,X1,X2),X1)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)),X0)
        & v4_pre_topc(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f92,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f63,f65])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ~ v5_pre_topc(sK2,sK0,sK3) ),
    inference(backward_demodulation,[],[f66,f65])).

fof(f66,plain,(
    ~ v5_pre_topc(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f62,f65])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f110,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f56,f60,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f60,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f629,plain,(
    v4_pre_topc(k10_relat_1(sK2,sK5(sK0,sK3,sK2)),sK0) ),
    inference(backward_demodulation,[],[f264,f628])).

fof(f628,plain,(
    k10_relat_1(sK2,sK5(sK0,sK3,sK2)) = k10_relat_1(sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))) ),
    inference(superposition,[],[f283,f343])).

fof(f343,plain,(
    sK5(sK0,sK3,sK2) = k3_xboole_0(u1_struct_0(sK3),sK6(sK1,sK3,sK5(sK0,sK3,sK2))) ),
    inference(unit_resulting_resolution,[],[f151,f150,f233])).

fof(f233,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | k3_xboole_0(u1_struct_0(sK3),sK6(sK1,sK3,X0)) = X0
      | ~ v4_pre_topc(X0,sK3) ) ),
    inference(forward_demodulation,[],[f232,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f232,plain,(
    ! [X0] :
      ( k3_xboole_0(sK6(sK1,sK3,X0),u1_struct_0(sK3)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(X0,sK3) ) ),
    inference(forward_demodulation,[],[f231,f196])).

fof(f196,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK3),X0,u1_struct_0(sK3)) = k3_xboole_0(X0,u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f122,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f122,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f119,f120])).

fof(f120,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f115,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f115,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f110,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f119,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f115,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f231,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK3),sK6(sK1,sK3,X0),u1_struct_0(sK3)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(X0,sK3) ) ),
    inference(forward_demodulation,[],[f229,f120])).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v4_pre_topc(X0,sK3)
      | k9_subset_1(u1_struct_0(sK3),sK6(sK1,sK3,X0),k2_struct_0(sK3)) = X0 ) ),
    inference(resolution,[],[f100,f60])).

fof(f100,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X3,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v4_pre_topc(X2,X3)
      | k9_subset_1(u1_struct_0(X3),sK6(sK1,X3,X2),k2_struct_0(X3)) = X2 ) ),
    inference(resolution,[],[f56,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK6(X0,X1,X2),X0)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f150,plain,(
    m1_subset_1(sK5(sK0,sK3,sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f55,f110,f93,f90,f92,f91,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f151,plain,(
    v4_pre_topc(sK5(sK0,sK3,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f55,f110,f93,f90,f92,f91,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v4_pre_topc(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f283,plain,(
    ! [X5] : k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK3),X5)) = k10_relat_1(sK2,X5) ),
    inference(forward_demodulation,[],[f282,f281])).

fof(f281,plain,(
    ! [X4] : k10_relat_1(sK2,X4) = k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK1),X4)) ),
    inference(forward_demodulation,[],[f280,f144])).

fof(f144,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f134,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f134,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f280,plain,(
    ! [X4] : k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X4)) = k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK1),X4)) ),
    inference(forward_demodulation,[],[f268,f143])).

fof(f143,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(unit_resulting_resolution,[],[f93,f134,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(f268,plain,(
    ! [X4] : k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X4)) = k3_xboole_0(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,X4)) ),
    inference(superposition,[],[f143,f223])).

fof(f223,plain,(
    k10_relat_1(sK2,u1_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f144,f166])).

fof(f166,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f147,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f147,plain,(
    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f142,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f142,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f132,f133])).

fof(f133,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

% (17299)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f132,plain,(
    m1_subset_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f59,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f282,plain,(
    ! [X5] : k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK3),X5)) = k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK1),X5)) ),
    inference(forward_demodulation,[],[f269,f143])).

fof(f269,plain,(
    ! [X5] : k10_relat_1(sK2,k3_xboole_0(u1_struct_0(sK3),X5)) = k3_xboole_0(k10_relat_1(sK2,u1_struct_0(sK1)),k10_relat_1(sK2,X5)) ),
    inference(superposition,[],[f143,f227])).

fof(f227,plain,(
    k10_relat_1(sK2,u1_struct_0(sK1)) = k10_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f224,f223])).

fof(f224,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(superposition,[],[f144,f174])).

fof(f174,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f169,f81])).

fof(f169,plain,(
    r1_tarski(k2_relat_1(sK2),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f164,f82])).

fof(f164,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f154,f155])).

fof(f155,plain,(
    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f91,f85])).

fof(f154,plain,(
    m1_subset_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK3),sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f91,f86])).

fof(f264,plain,(
    v4_pre_topc(k10_relat_1(sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))),sK0) ),
    inference(forward_demodulation,[],[f259,f131])).

fof(f131,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ),
    inference(unit_resulting_resolution,[],[f59,f88])).

fof(f259,plain,(
    v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK6(sK1,sK3,sK5(sK0,sK3,sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f55,f56,f61,f58,f59,f205,f204,f103])).

fof(f103,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v5_pre_topc(sK2,X4,X3)
      | ~ v4_pre_topc(X2,X3)
      | ~ v1_funct_2(sK2,u1_struct_0(X4),u1_struct_0(X3))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X4),u1_struct_0(X3),sK2,X2),X4)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f93,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f204,plain,(
    m1_subset_1(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f56,f60,f151,f150,f75])).

% (17300)Refutation not found, incomplete strategy% (17300)------------------------------
% (17300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17300)Termination reason: Refutation not found, incomplete strategy

% (17300)Memory used [KB]: 6396
% (17300)Time elapsed: 0.089 s
% (17300)------------------------------
% (17300)------------------------------
fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f205,plain,(
    v4_pre_topc(sK6(sK1,sK3,sK5(sK0,sK3,sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f60,f151,f150,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | v4_pre_topc(sK6(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

%------------------------------------------------------------------------------
