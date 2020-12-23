%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1769+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 5.40s
% Output     : Refutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :   80 (1465 expanded)
%              Number of leaves         :   14 ( 738 expanded)
%              Depth                    :   15
%              Number of atoms          :  635 (37011 expanded)
%              Number of equality atoms :   46 (1962 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8964,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8962,f8963])).

fof(f8963,plain,(
    r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25) ),
    inference(duplicate_literal_removal,[],[f8955])).

fof(f8955,plain,
    ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25)
    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25) ),
    inference(backward_demodulation,[],[f8669,f8953])).

fof(f8953,plain,(
    k3_tmap_1(sK20,sK21,sK20,sK22,sK24) = k7_relat_1(sK24,u1_struct_0(sK22)) ),
    inference(forward_demodulation,[],[f8931,f6287])).

fof(f6287,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK20),u1_struct_0(sK21),sK24,X0) = k7_relat_1(sK24,X0) ),
    inference(unit_resulting_resolution,[],[f4156,f4158,f4318])).

fof(f4318,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3586])).

fof(f3586,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3585])).

fof(f3585,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1554])).

fof(f1554,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f4158,plain,(
    m1_subset_1(sK24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21)))) ),
    inference(cnf_transformation,[],[f3872])).

fof(f3872,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
      | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) )
    & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
      | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) )
    & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,sK26)
    & sK20 = sK23
    & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
    & v1_funct_2(sK26,u1_struct_0(sK23),u1_struct_0(sK21))
    & v1_funct_1(sK26)
    & m1_subset_1(sK25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
    & v1_funct_2(sK25,u1_struct_0(sK22),u1_struct_0(sK21))
    & v1_funct_1(sK25)
    & m1_subset_1(sK24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
    & v1_funct_2(sK24,u1_struct_0(sK20),u1_struct_0(sK21))
    & v1_funct_1(sK24)
    & m1_pre_topc(sK23,sK20)
    & ~ v2_struct_0(sK23)
    & m1_pre_topc(sK22,sK20)
    & ~ v2_struct_0(sK22)
    & l1_pre_topc(sK21)
    & v2_pre_topc(sK21)
    & ~ v2_struct_0(sK21)
    & l1_pre_topc(sK20)
    & v2_pre_topc(sK20)
    & ~ v2_struct_0(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22,sK23,sK24,sK25,sK26])],[f3864,f3871,f3870,f3869,f3868,f3867,f3866,f3865])).

fof(f3865,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK20,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK20,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK20,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK20,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK20),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK20 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK20)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK20)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK20)
      & v2_pre_topc(sK20)
      & ~ v2_struct_0(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f3866,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK20,X1,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK20,X1,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK20,X1,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK20,X1,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(sK20),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                            & sK20 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK20)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK20)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(X3),u1_struct_0(sK21),X4,X6)
                          & sK20 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK21))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK21))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK21))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK21))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
                  & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK20)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK20)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK21)
      & v2_pre_topc(sK21)
      & ~ v2_struct_0(sK21) ) ),
    introduced(choice_axiom,[])).

fof(f3867,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,X2),X5)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,X2,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,X2),X5)
                          | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,X2,X6),X5) )
                        & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(X3),u1_struct_0(sK21),X4,X6)
                        & sK20 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK21))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK21))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK21))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK21))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
                & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK20)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK20)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                        | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,sK22,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                        | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,sK22,X6),X5) )
                      & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(X3),u1_struct_0(sK21),X4,X6)
                      & sK20 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK21))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK21))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
                  & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
              & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK20)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK22,sK20)
      & ~ v2_struct_0(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f3868,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                      | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,sK22,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                      | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,X3,sK22,X6),X5) )
                    & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(X3),u1_struct_0(sK21),X4,X6)
                    & sK20 = X3
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK21))))
                    & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK21))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
                & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
            & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK20)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
                  & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),X4,X6)
                  & sK20 = sK23
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
                  & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
              & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
          & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK23,sK20)
      & ~ v2_struct_0(sK23) ) ),
    introduced(choice_axiom,[])).

fof(f3869,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                  | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
                & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,X4,sK22),X5)
                  | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
                & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),X4,X6)
                & sK20 = sK23
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
                & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
            & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
        & v1_funct_2(X4,u1_struct_0(sK20),u1_struct_0(sK21))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),X5)
                | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
              & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),X5)
                | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
              & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,X6)
              & sK20 = sK23
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
              & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
          & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
          & v1_funct_1(X5) )
      & m1_subset_1(sK24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21))))
      & v1_funct_2(sK24,u1_struct_0(sK20),u1_struct_0(sK21))
      & v1_funct_1(sK24) ) ),
    introduced(choice_axiom,[])).

fof(f3870,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),X5)
              | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
            & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),X5)
              | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),X5) )
            & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,X6)
            & sK20 = sK23
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
            & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
            & v1_funct_1(X6) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
        & v1_funct_2(X5,u1_struct_0(sK22),u1_struct_0(sK21))
        & v1_funct_1(X5) )
   => ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
            | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),sK25) )
          & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
            | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),sK25) )
          & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,X6)
          & sK20 = sK23
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
          & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
          & v1_funct_1(X6) )
      & m1_subset_1(sK25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK22),u1_struct_0(sK21))))
      & v1_funct_2(sK25,u1_struct_0(sK22),u1_struct_0(sK21))
      & v1_funct_1(sK25) ) ),
    introduced(choice_axiom,[])).

fof(f3871,plain,
    ( ? [X6] :
        ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
          | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),sK25) )
        & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
          | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,X6),sK25) )
        & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,X6)
        & sK20 = sK23
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
        & v1_funct_2(X6,u1_struct_0(sK23),u1_struct_0(sK21))
        & v1_funct_1(X6) )
   => ( ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
        | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) )
      & ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
        | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) )
      & r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,sK26)
      & sK20 = sK23
      & m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21))))
      & v1_funct_2(sK26,u1_struct_0(sK23),u1_struct_0(sK21))
      & v1_funct_1(sK26) ) ),
    introduced(choice_axiom,[])).

fof(f3864,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3863])).

fof(f3863,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3444])).

fof(f3444,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3443])).

fof(f3443,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3434])).

fof(f3434,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3433])).

fof(f3433,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

fof(f4156,plain,(
    v1_funct_1(sK24) ),
    inference(cnf_transformation,[],[f3872])).

fof(f8931,plain,(
    k3_tmap_1(sK20,sK21,sK20,sK22,sK24) = k2_partfun1(u1_struct_0(sK20),u1_struct_0(sK21),sK24,u1_struct_0(sK22)) ),
    inference(unit_resulting_resolution,[],[f4894,f4147,f4148,f4149,f4150,f4151,f4893,f4153,f4156,f4153,f4157,f4158,f4213])).

fof(f4213,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3494])).

fof(f3494,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3493])).

fof(f3493,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f4157,plain,(
    v1_funct_2(sK24,u1_struct_0(sK20),u1_struct_0(sK21)) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4153,plain,(
    m1_pre_topc(sK22,sK20) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4893,plain,(
    m1_pre_topc(sK20,sK20) ),
    inference(forward_demodulation,[],[f4155,f4165])).

fof(f4165,plain,(
    sK20 = sK23 ),
    inference(cnf_transformation,[],[f3872])).

fof(f4155,plain,(
    m1_pre_topc(sK23,sK20) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4151,plain,(
    l1_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4150,plain,(
    v2_pre_topc(sK21) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4149,plain,(
    ~ v2_struct_0(sK21) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4148,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4147,plain,(
    v2_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4894,plain,(
    ~ v2_struct_0(sK20) ),
    inference(forward_demodulation,[],[f4154,f4165])).

fof(f4154,plain,(
    ~ v2_struct_0(sK23) ),
    inference(cnf_transformation,[],[f3872])).

fof(f8669,plain,
    ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK24),sK25)
    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25) ),
    inference(backward_demodulation,[],[f8289,f8665])).

fof(f8665,plain,(
    k2_tmap_1(sK20,sK21,sK24,sK22) = k7_relat_1(sK24,u1_struct_0(sK22)) ),
    inference(forward_demodulation,[],[f8651,f6287])).

fof(f8651,plain,(
    k2_tmap_1(sK20,sK21,sK24,sK22) = k2_partfun1(u1_struct_0(sK20),u1_struct_0(sK21),sK24,u1_struct_0(sK22)) ),
    inference(unit_resulting_resolution,[],[f4894,f4147,f4148,f4149,f4150,f4151,f4156,f4153,f4157,f4158,f4175])).

fof(f4175,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3450])).

fof(f3450,plain,(
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
    inference(flattening,[],[f3449])).

fof(f3449,plain,(
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
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f8289,plain,
    ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK24),sK25)
    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25) ),
    inference(backward_demodulation,[],[f4889,f8282])).

fof(f8282,plain,(
    sK24 = sK26 ),
    inference(unit_resulting_resolution,[],[f4156,f4162,f5035,f5035,f4157,f4892,f4158,f4888,f4891,f4214])).

fof(f4214,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f3886])).

fof(f3886,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f3496])).

fof(f3496,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f3495])).

fof(f3495,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3239])).

fof(f3239,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f4891,plain,(
    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK20),u1_struct_0(sK21)))) ),
    inference(forward_demodulation,[],[f4164,f4165])).

fof(f4164,plain,(
    m1_subset_1(sK26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK23),u1_struct_0(sK21)))) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4888,plain,(
    r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK20),u1_struct_0(sK21),sK24,sK26) ),
    inference(backward_demodulation,[],[f4166,f4165])).

fof(f4166,plain,(
    r1_funct_2(u1_struct_0(sK20),u1_struct_0(sK21),u1_struct_0(sK23),u1_struct_0(sK21),sK24,sK26) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4892,plain,(
    v1_funct_2(sK26,u1_struct_0(sK20),u1_struct_0(sK21)) ),
    inference(forward_demodulation,[],[f4163,f4165])).

fof(f4163,plain,(
    v1_funct_2(sK26,u1_struct_0(sK23),u1_struct_0(sK21)) ),
    inference(cnf_transformation,[],[f3872])).

fof(f5035,plain,(
    ~ v1_xboole_0(u1_struct_0(sK21)) ),
    inference(unit_resulting_resolution,[],[f4149,f4930,f4265])).

fof(f4265,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3547])).

fof(f3547,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3546])).

fof(f3546,plain,(
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

fof(f4930,plain,(
    l1_struct_0(sK21) ),
    inference(unit_resulting_resolution,[],[f4151,f4268])).

fof(f4268,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3551])).

fof(f3551,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4162,plain,(
    v1_funct_1(sK26) ),
    inference(cnf_transformation,[],[f3872])).

fof(f4889,plain,
    ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK26),sK25)
    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25) ),
    inference(backward_demodulation,[],[f4167,f4165])).

fof(f4167,plain,
    ( r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
    | r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) ),
    inference(cnf_transformation,[],[f3872])).

fof(f8962,plain,(
    ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25) ),
    inference(duplicate_literal_removal,[],[f8956])).

fof(f8956,plain,
    ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25)
    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25) ),
    inference(backward_demodulation,[],[f8670,f8953])).

fof(f8670,plain,
    ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k7_relat_1(sK24,u1_struct_0(sK22)),sK25)
    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK24),sK25) ),
    inference(backward_demodulation,[],[f8290,f8665])).

fof(f8290,plain,
    ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK24),sK25) ),
    inference(backward_demodulation,[],[f4890,f8282])).

fof(f4890,plain,
    ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK20,sK22,sK26),sK25) ),
    inference(backward_demodulation,[],[f4168,f4165])).

fof(f4168,plain,
    ( ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k2_tmap_1(sK20,sK21,sK24,sK22),sK25)
    | ~ r2_funct_2(u1_struct_0(sK22),u1_struct_0(sK21),k3_tmap_1(sK20,sK21,sK23,sK22,sK26),sK25) ),
    inference(cnf_transformation,[],[f3872])).
%------------------------------------------------------------------------------
