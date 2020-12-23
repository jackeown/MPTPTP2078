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
% DateTime   : Thu Dec  3 13:19:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 (3495 expanded)
%              Number of leaves         :   19 (1869 expanded)
%              Depth                    :   17
%              Number of atoms          : 1073 (85580 expanded)
%              Number of equality atoms :  106 (12917 expanded)
%              Maximal formula depth    :   30 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f91,f92,f160,f171,f182])).

fof(f182,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f94,f54,f93,f80,f175,f142])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0)
      | ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0)
      | ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK1) ) ),
    inference(forward_demodulation,[],[f140,f120])).

fof(f120,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f111,f114])).

fof(f114,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f46,f48,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f111,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f50,f47,f48,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
    & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
      | r1_tmap_1(sK0,sK1,sK2,sK5) )
    & sK5 = sK7
    & sK5 = sK6
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK0))
    & sK0 = k1_tsep_1(sK0,sK3,sK4)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                      | ~ r1_tmap_1(X0,X1,X2,X5) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | r1_tmap_1(X0,X1,X2,X5) )
                                    & X5 = X7
                                    & X5 = X6
                                    & m1_subset_1(X7,u1_struct_0(X4)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                    | r1_tmap_1(sK0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(sK0)) )
                      & sK0 = k1_tsep_1(sK0,X3,X4)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)
                                  | ~ r1_tmap_1(sK0,X1,X2,X5) )
                                & ( ( r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7)
                                    & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) )
                                  | r1_tmap_1(sK0,X1,X2,X5) )
                                & X5 = X7
                                & X5 = X6
                                & m1_subset_1(X7,u1_struct_0(X4)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(sK0)) )
                    & sK0 = k1_tsep_1(sK0,X3,X4)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)
                                | ~ r1_tmap_1(sK0,sK1,X2,X5) )
                              & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                  & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) )
                                | r1_tmap_1(sK0,sK1,X2,X5) )
                              & X5 = X7
                              & X5 = X6
                              & m1_subset_1(X7,u1_struct_0(X4)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(sK0)) )
                  & sK0 = k1_tsep_1(sK0,X3,X4)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (6868)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)
                              | ~ r1_tmap_1(sK0,sK1,X2,X5) )
                            & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7)
                                & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) )
                              | r1_tmap_1(sK0,sK1,X2,X5) )
                            & X5 = X7
                            & X5 = X6
                            & m1_subset_1(X7,u1_struct_0(X4)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(sK0)) )
                & sK0 = k1_tsep_1(sK0,X3,X4)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)
                            | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                          & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                              & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) )
                            | r1_tmap_1(sK0,sK1,sK2,X5) )
                          & X5 = X7
                          & X5 = X6
                          & m1_subset_1(X7,u1_struct_0(X4)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(sK0)) )
              & sK0 = k1_tsep_1(sK0,X3,X4)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)
                          | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                        & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                            & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) )
                          | r1_tmap_1(sK0,sK1,sK2,X5) )
                        & X5 = X7
                        & X5 = X6
                        & m1_subset_1(X7,u1_struct_0(X4)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,u1_struct_0(sK0)) )
            & sK0 = k1_tsep_1(sK0,X3,X4)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                        | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                      & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                          & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                        | r1_tmap_1(sK0,sK1,sK2,X5) )
                      & X5 = X7
                      & X5 = X6
                      & m1_subset_1(X7,u1_struct_0(X4)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,u1_struct_0(sK0)) )
          & sK0 = k1_tsep_1(sK0,sK3,X4)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                      | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                    & ( ( r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7)
                        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                      | r1_tmap_1(sK0,sK1,sK2,X5) )
                    & X5 = X7
                    & X5 = X6
                    & m1_subset_1(X7,u1_struct_0(X4)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,u1_struct_0(sK0)) )
        & sK0 = k1_tsep_1(sK0,sK3,X4)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                    | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                  & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                      & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                    | r1_tmap_1(sK0,sK1,sK2,X5) )
                  & X5 = X7
                  & X5 = X6
                  & m1_subset_1(X7,u1_struct_0(sK4)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,u1_struct_0(sK0)) )
      & sK0 = k1_tsep_1(sK0,sK3,sK4)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                  | ~ r1_tmap_1(sK0,sK1,sK2,X5) )
                & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                  | r1_tmap_1(sK0,sK1,sK2,X5) )
                & X5 = X7
                & X5 = X6
                & m1_subset_1(X7,u1_struct_0(sK4)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,u1_struct_0(sK0)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
                | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
              & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                  & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
                | r1_tmap_1(sK0,sK1,sK2,sK5) )
              & sK5 = X7
              & sK5 = X6
              & m1_subset_1(X7,u1_struct_0(sK4)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)
              | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
            & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
                & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) )
              | r1_tmap_1(sK0,sK1,sK2,sK5) )
            & sK5 = X7
            & sK5 = X6
            & m1_subset_1(X7,u1_struct_0(sK4)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
            | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
          & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
              & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
            | r1_tmap_1(sK0,sK1,sK2,sK5) )
          & sK5 = X7
          & sK5 = sK6
          & m1_subset_1(X7,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
          | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
        & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7)
            & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
          | r1_tmap_1(sK0,sK1,sK2,sK5) )
        & sK5 = X7
        & sK5 = sK6
        & m1_subset_1(X7,u1_struct_0(sK4)) )
   => ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
        | ~ r1_tmap_1(sK0,sK1,sK2,sK5) )
      & ( ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
          & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) )
        | r1_tmap_1(sK0,sK1,sK2,sK5) )
      & sK5 = sK7
      & sK5 = sK6
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
                                    | ~ r1_tmap_1(X0,X1,X2,X5) )
                                  & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    | r1_tmap_1(X0,X1,X2,X5) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X0,X1,X2,X5)
                                  <~> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  & X5 = X7
                                  & X5 = X6
                                  & m1_subset_1(X7,u1_struct_0(X4)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X4))
                                     => ( ( X5 = X7
                                          & X5 = X6 )
                                       => ( r1_tmap_1(X0,X1,X2,X5)
                                        <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                            & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( ( X5 = X7
                                        & X5 = X6 )
                                     => ( r1_tmap_1(X0,X1,X2,X5)
                                      <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                          & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK1) ) ),
    inference(superposition,[],[f108,f123])).

fof(f123,plain,(
    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f117,f122])).

fof(f122,plain,(
    sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f116,f115,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f115,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f48,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f117,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f113,f114])).

fof(f113,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f97,f47,f48,f63])).

fof(f97,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f42,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ v1_funct_1(X4)
      | r1_tmap_1(sK3,X3,k2_tmap_1(sK0,X3,X4,sK3),X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ v2_pre_topc(X3) ) ),
    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5)
      | r1_tmap_1(sK3,X3,k2_tmap_1(sK0,X3,X4,sK3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f53])).

fof(f53,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                    & ( ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) )
                                      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                  <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                      & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) )
                                  | X5 != X7
                                  | X5 != X6
                                  | ~ m1_subset_1(X7,u1_struct_0(X4)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) )
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( ( X5 = X7
                                      & X5 = X6 )
                                   => ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
                                    <=> ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
                                        & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f175,plain,
    ( ~ r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f174,f120])).

fof(f174,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | spl8_2 ),
    inference(forward_demodulation,[],[f85,f57])).

fof(f57,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,
    ( ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_2
  <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f80,plain,
    ( r1_tmap_1(sK0,sK1,sK2,sK5)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_1
  <=> r1_tmap_1(sK0,sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f58,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f55,f57])).

fof(f55,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f171,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f94,f93,f54,f80,f162,f146])).

fof(f146,plain,(
    ! [X0] :
      ( r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1) ) ),
    inference(forward_demodulation,[],[f144,f118])).

fof(f118,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f112,f114])).

fof(f112,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f52,f47,f48,f63])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0)
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f109,f123])).

fof(f109,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tmap_1(sK0,X9,k2_tmap_1(sK0,X9,X10,sK0),X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK3))
      | ~ v2_pre_topc(X9)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | r1_tmap_1(sK4,X9,k2_tmap_1(sK0,X9,X10,sK4),X11)
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))
      | v2_struct_0(X9)
      | ~ m1_subset_1(X11,u1_struct_0(sK4))
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X9))
      | ~ l1_pre_topc(X9) ) ),
    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f105])).

fof(f105,plain,(
    ! [X10,X11,X9] :
      ( ~ r1_tmap_1(sK0,X9,k2_tmap_1(sK0,X9,X10,sK0),X11)
      | r1_tmap_1(sK4,X9,k2_tmap_1(sK0,X9,X10,sK4),X11)
      | ~ m1_subset_1(X11,u1_struct_0(sK4))
      | ~ m1_subset_1(X11,u1_struct_0(sK3))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9))))
      | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X9))
      | ~ v1_funct_1(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f75,f53])).

fof(f75,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f162,plain,
    ( ~ r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK5)
    | spl8_3 ),
    inference(forward_demodulation,[],[f161,f118])).

fof(f161,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | spl8_3 ),
    inference(forward_demodulation,[],[f89,f58])).

fof(f89,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_3
  <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f160,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f93,f94,f54,f81,f121,f119,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0) ) ),
    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r1_tmap_1(sK0,sK1,sK2,X0)
      | ~ r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0)
      | ~ r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(forward_demodulation,[],[f149,f123])).

fof(f149,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0)
      | ~ r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0) ) ),
    inference(forward_demodulation,[],[f148,f120])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0) ) ),
    inference(superposition,[],[f110,f118])).

fof(f110,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tmap_1(sK4,X15,k2_tmap_1(sK0,X15,X16,sK4),X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,X15,k2_tmap_1(sK0,X15,X16,sK3),X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK4))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | v2_struct_0(X15)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X15))
      | ~ v1_funct_1(X16)
      | r1_tmap_1(sK0,X15,k2_tmap_1(sK0,X15,X16,sK0),X17) ) ),
    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f107])).

fof(f107,plain,(
    ! [X17,X15,X16] :
      ( r1_tmap_1(sK0,X15,k2_tmap_1(sK0,X15,X16,sK0),X17)
      | ~ r1_tmap_1(sK4,X15,k2_tmap_1(sK0,X15,X16,sK4),X17)
      | ~ r1_tmap_1(sK3,X15,k2_tmap_1(sK0,X15,X16,sK3),X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK4))
      | ~ m1_subset_1(X17,u1_struct_0(sK3))
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | ~ m1_pre_topc(sK4,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15))))
      | ~ v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X15))
      | ~ v1_funct_1(X16)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f73,f53])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X6 != X7
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5)
      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)
      | X5 != X7
      | X5 != X6
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,
    ( r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK5)
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f95,f118])).

fof(f95,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5)
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f88,f58])).

fof(f88,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f121,plain,
    ( r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK5)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f96,f120])).

fof(f96,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f84,f57])).

fof(f84,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f81,plain,
    ( ~ r1_tmap_1(sK0,sK1,sK2,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f59,f83,f79])).

fof(f59,plain,
    ( r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f60,f87,f79])).

fof(f60,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f61,f87,f83,f79])).

fof(f61,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK0,sK1,sK2,sK5) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6876)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (6883)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (6871)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (6886)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (6870)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (6878)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (6879)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (6875)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (6880)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (6867)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (6878)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f90,f91,f92,f160,f171,f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ~spl8_1 | spl8_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    $false | (~spl8_1 | spl8_2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f94,f54,f93,f80,f175,f142])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.20/0.49    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f140,f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f111,f114])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f46,f48,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK3))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f50,f47,f48,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ((((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f28,f36,f35,f34,f33,f32,f31,f30,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6) | ~r1_tmap_1(sK0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(sK0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X2,X3),X6)) | r1_tmap_1(sK0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  % (6868)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6) | ~r1_tmap_1(sK0,sK1,X2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,X2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X2,X3),X6)) | r1_tmap_1(sK0,sK1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,sK2,X3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,X3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(X4,sK1,k2_tmap_1(sK0,sK1,sK2,X4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,X4) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) & sK0 = k1_tsep_1(sK0,sK3,sK4) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,X5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK0))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ? [X6] : (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = X6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ? [X7] : ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = X7 & sK5 = sK6 & m1_subset_1(X7,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)) & ((r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)) | r1_tmap_1(sK0,sK1,sK2,sK5)) & sK5 = sK7 & sK5 = sK6 & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5)) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((((~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(X0,X1,X2,X5)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | r1_tmap_1(X0,X1,X2,X5))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & X5 = X7 & X5 = X6 & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X0,X1,X2,X5) <~> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & (X5 = X7 & X5 = X6)) & m1_subset_1(X7,u1_struct_0(X4))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X0))) & k1_tsep_1(X0,X3,X4) = X0) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (k1_tsep_1(X0,X3,X4) = X0 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(X0,X1,X2,X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)))))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK1)) )),
% 0.20/0.49    inference(superposition,[],[f108,f123])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f117,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f116,f115,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f48,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f48,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK0) = k7_relat_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(forward_demodulation,[],[f113,f114])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f97,f47,f48,f63])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    m1_pre_topc(sK0,sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f42,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~l1_pre_topc(X3) | v2_struct_0(X3) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~v1_funct_1(X4) | r1_tmap_1(sK3,X3,k2_tmap_1(sK0,X3,X4,sK3),X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~v2_pre_topc(X3)) )),
% 0.20/0.49    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tmap_1(sK0,X3,k2_tmap_1(sK0,X3,X4,sK0),X5) | r1_tmap_1(sK3,X3,k2_tmap_1(sK0,X3,X4,sK3),X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~v1_funct_1(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f77,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | (~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) & ((r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6)) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))) | (X5 != X7 | X5 != X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4)))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X4)) => ((X5 = X7 & X5 = X6) => (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) <=> (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6))))))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ~v2_struct_0(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    m1_pre_topc(sK4,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    v2_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK5) | spl8_2),
% 0.20/0.49    inference(forward_demodulation,[],[f174,f120])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | spl8_2),
% 0.20/0.49    inference(forward_demodulation,[],[f85,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    sK5 = sK6),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl8_2 <=> r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    r1_tmap_1(sK0,sK1,sK2,sK5) | ~spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl8_1 <=> r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.49    inference(forward_demodulation,[],[f56,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    sK5 = sK7),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.49    inference(forward_demodulation,[],[f55,f57])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ~spl8_1 | spl8_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    $false | (~spl8_1 | spl8_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f94,f93,f54,f80,f162,f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.20/0.49    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f144,f118])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))),
% 0.20/0.49    inference(forward_demodulation,[],[f112,f114])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    k2_tmap_1(sK0,sK1,sK2,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK4))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f41,f42,f43,f44,f45,f46,f52,f47,f48,f63])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tmap_1(sK0,sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),X0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1)) )),
% 0.20/0.49    inference(superposition,[],[f109,f123])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r1_tmap_1(sK0,X9,k2_tmap_1(sK0,X9,X10,sK0),X11) | ~m1_subset_1(X11,u1_struct_0(sK3)) | ~v2_pre_topc(X9) | ~m1_subset_1(X11,u1_struct_0(sK0)) | r1_tmap_1(sK4,X9,k2_tmap_1(sK0,X9,X10,sK4),X11) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) | v2_struct_0(X9) | ~m1_subset_1(X11,u1_struct_0(sK4)) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X9)) | ~l1_pre_topc(X9)) )),
% 0.20/0.49    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X10,X11,X9] : (~r1_tmap_1(sK0,X9,k2_tmap_1(sK0,X9,X10,sK0),X11) | r1_tmap_1(sK4,X9,k2_tmap_1(sK0,X9,X10,sK4),X11) | ~m1_subset_1(X11,u1_struct_0(sK4)) | ~m1_subset_1(X11,u1_struct_0(sK3)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X9)))) | ~v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(X9)) | ~v1_funct_1(X10) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f75,f53])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK5) | spl8_3),
% 0.20/0.49    inference(forward_demodulation,[],[f161,f118])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | spl8_3),
% 0.20/0.49    inference(forward_demodulation,[],[f89,f58])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl8_3 <=> r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    $false | (spl8_1 | ~spl8_2 | ~spl8_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f93,f94,f54,f81,f121,f119,f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_tmap_1(sK0,sK1,sK2,X0) | ~r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0)) )),
% 0.20/0.49    inference(global_subsumption,[],[f48,f47,f46,f45,f44,f43,f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tmap_1(sK0,sK1,sK2,X0) | ~r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0) | ~r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f149,f123])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),X0) | ~r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f148,f120])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | r1_tmap_1(sK0,sK1,k2_tmap_1(sK0,sK1,sK2,sK0),X0)) )),
% 0.20/0.49    inference(superposition,[],[f110,f118])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X17,X15,X16] : (~r1_tmap_1(sK4,X15,k2_tmap_1(sK0,X15,X16,sK4),X17) | ~m1_subset_1(X17,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,X15,k2_tmap_1(sK0,X15,X16,sK3),X17) | ~m1_subset_1(X17,u1_struct_0(sK4)) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) | ~m1_subset_1(X17,u1_struct_0(sK0)) | v2_struct_0(X15) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X15)) | ~v1_funct_1(X16) | r1_tmap_1(sK0,X15,k2_tmap_1(sK0,X15,X16,sK0),X17)) )),
% 0.20/0.49    inference(global_subsumption,[],[f52,f51,f50,f49,f42,f41,f40,f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X17,X15,X16] : (r1_tmap_1(sK0,X15,k2_tmap_1(sK0,X15,X16,sK0),X17) | ~r1_tmap_1(sK4,X15,k2_tmap_1(sK0,X15,X16,sK4),X17) | ~r1_tmap_1(sK3,X15,k2_tmap_1(sK0,X15,X16,sK3),X17) | ~m1_subset_1(X17,u1_struct_0(sK4)) | ~m1_subset_1(X17,u1_struct_0(sK3)) | ~m1_subset_1(X17,u1_struct_0(sK0)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X15)))) | ~v1_funct_2(X16,u1_struct_0(sK0),u1_struct_0(X15)) | ~v1_funct_1(X16) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.49    inference(superposition,[],[f73,f53])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X7) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X6 != X7 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(k1_tsep_1(X0,X3,X4),X1,k2_tmap_1(X0,X1,X2,k1_tsep_1(X0,X3,X4)),X5) | ~r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X7) | ~r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X2,X3),X6) | X5 != X7 | X5 != X6 | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X3,X4))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k7_relat_1(sK2,u1_struct_0(sK4)),sK5) | ~spl8_3),
% 0.20/0.49    inference(backward_demodulation,[],[f95,f118])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK5) | ~spl8_3),
% 0.20/0.49    inference(forward_demodulation,[],[f88,f58])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~spl8_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k7_relat_1(sK2,u1_struct_0(sK3)),sK5) | ~spl8_2),
% 0.20/0.49    inference(backward_demodulation,[],[f96,f120])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK5) | ~spl8_2),
% 0.20/0.49    inference(forward_demodulation,[],[f84,f57])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~spl8_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ~r1_tmap_1(sK0,sK1,sK2,sK5) | spl8_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl8_1 | spl8_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f59,f83,f79])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl8_1 | spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f60,f87,f79])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f61,f87,f83,f79])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK0,sK1,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK2,sK3),sK6) | ~r1_tmap_1(sK0,sK1,sK2,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6878)------------------------------
% 0.20/0.49  % (6878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6878)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6878)Memory used [KB]: 11129
% 0.20/0.49  % (6878)Time elapsed: 0.087 s
% 0.20/0.49  % (6878)------------------------------
% 0.20/0.49  % (6878)------------------------------
% 0.20/0.49  % (6881)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (6868)Refutation not found, incomplete strategy% (6868)------------------------------
% 0.20/0.49  % (6868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6868)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (6868)Memory used [KB]: 10618
% 0.20/0.49  % (6868)Time elapsed: 0.091 s
% 0.20/0.49  % (6868)------------------------------
% 0.20/0.49  % (6868)------------------------------
% 0.20/0.49  % (6869)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (6873)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (6884)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (6877)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (6866)Success in time 0.15 s
%------------------------------------------------------------------------------
