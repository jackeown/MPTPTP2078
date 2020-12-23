%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:06 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 794 expanded)
%              Number of leaves         :   25 ( 402 expanded)
%              Depth                    :   42
%              Number of atoms          : 1209 (12663 expanded)
%              Number of equality atoms :   61 (1598 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f690,f771,f1850])).

fof(f1850,plain,
    ( ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f1849])).

fof(f1849,plain,
    ( $false
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f1848,f176])).

fof(f176,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f172,f62])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f50,f49,f48,f47,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK3,X4,X5)
                          & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK3,X4,X5)
                        & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK3,X4,X5)
                      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK3,X4,X5)
                    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                  & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
              & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
            & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
          & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
        & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f172,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1848,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f1846,f679])).

fof(f679,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f678])).

fof(f678,plain,
    ( spl9_18
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f1846,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl9_17 ),
    inference(resolution,[],[f1845,f226])).

fof(f226,plain,(
    ! [X0] :
      ( m1_pre_topc(sK5,X0)
      | ~ m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f86,f73])).

fof(f73,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f1845,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1844,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f1844,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1843,f193])).

fof(f193,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f192,f61])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f192,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f188,f62])).

fof(f188,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f93,f67])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f1843,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1842,f176])).

fof(f1842,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ spl9_17 ),
    inference(duplicate_literal_removal,[],[f1841])).

fof(f1841,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ spl9_17 ),
    inference(resolution,[],[f1840,f1080])).

fof(f1080,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK4,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,X0) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1079,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1079,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1078,f64])).

fof(f64,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1078,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1077,f65])).

fof(f65,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f1077,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1076,f66])).

fof(f1076,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1075,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f1075,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1074,f70])).

fof(f70,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f1074,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1073,f71])).

fof(f71,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1073,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1072,f72])).

fof(f72,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1072,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1071,f655])).

fof(f655,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl9_17
  <=> m1_pre_topc(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f1071,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,sK5)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1070,f74])).

fof(f74,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1070,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1069,f113])).

fof(f113,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f76,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1069,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1068,f78])).

fof(f78,plain,(
    ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f1068,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK5,sK3,sK6,sK7)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(duplicate_literal_removal,[],[f1051])).

fof(f1051,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK5,sK3,sK6,sK7)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_17 ),
    inference(resolution,[],[f1039,f602])).

fof(f602,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | r1_tmap_1(X3,X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f112,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f112,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X5)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X0,X4,X5)
                                  | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f1039,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1038,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1038,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1037,f61])).

fof(f1037,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1036,f62])).

fof(f1036,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1035,f69])).

fof(f69,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1035,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1034,f63])).

fof(f1034,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1033,f64])).

fof(f1033,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1032,f65])).

fof(f1032,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1031,f70])).

fof(f1031,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1030,f71])).

fof(f1030,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1029,f72])).

fof(f1029,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f951,f655])).

fof(f951,plain,(
    ! [X0] :
      ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
      | ~ m1_pre_topc(sK4,sK5)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK5,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f114,f522])).

fof(f522,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f521])).

fof(f521,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f375,f375])).

fof(f375,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f89,f94])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f114,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f77,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f1840,plain,(
    ! [X1] :
      ( v1_tsep_1(X1,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f1838,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1838,plain,(
    ! [X0] :
      ( sP0(X0,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1837,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1837,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X0,X0)
      | sP0(X0,X0) ) ),
    inference(subsumption_resolution,[],[f1836,f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1836,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X0,X0)
      | sP0(X0,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1833])).

fof(f1833,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X0,X0)
      | sP0(X0,X0)
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f371,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k2_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | sP0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f284,f79])).

fof(f79,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f284,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f272,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f272,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f108,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f40,f42,f41])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f771,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f770,f654])).

fof(f770,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(subsumption_resolution,[],[f769,f177])).

fof(f177,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f173,f62])).

fof(f173,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f82,f69])).

fof(f769,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f768,f195])).

fof(f195,plain,(
    v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f194,f61])).

fof(f194,plain,
    ( v2_pre_topc(sK5)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f189,plain,
    ( v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f93,f69])).

fof(f768,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f767,f193])).

fof(f767,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f753,f176])).

fof(f753,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(superposition,[],[f339,f73])).

fof(f339,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f325,f81])).

fof(f325,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f105,f82])).

fof(f105,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f690,plain,(
    spl9_18 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | spl9_18 ),
    inference(subsumption_resolution,[],[f686,f176])).

fof(f686,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_18 ),
    inference(resolution,[],[f680,f81])).

fof(f680,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:17:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (1484)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (1482)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (1472)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (1477)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (1491)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (1477)Refutation not found, incomplete strategy% (1477)------------------------------
% 0.20/0.51  % (1477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1477)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1477)Memory used [KB]: 6268
% 0.20/0.51  % (1477)Time elapsed: 0.096 s
% 0.20/0.51  % (1477)------------------------------
% 0.20/0.51  % (1477)------------------------------
% 0.20/0.51  % (1476)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (1492)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (1483)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (1490)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (1481)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (1480)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (1478)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (1479)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (1494)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (1486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (1472)Refutation not found, incomplete strategy% (1472)------------------------------
% 0.20/0.53  % (1472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1472)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1472)Memory used [KB]: 10874
% 0.20/0.53  % (1472)Time elapsed: 0.097 s
% 0.20/0.53  % (1472)------------------------------
% 0.20/0.53  % (1472)------------------------------
% 0.20/0.53  % (1493)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (1485)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (1475)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (1474)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (1473)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (1497)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.55  % (1496)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (1495)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.49/0.56  % (1489)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.49/0.56  % (1488)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.49/0.56  % (1487)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.30/0.69  % (1476)Refutation found. Thanks to Tanya!
% 2.30/0.69  % SZS status Theorem for theBenchmark
% 2.30/0.69  % SZS output start Proof for theBenchmark
% 2.30/0.69  fof(f1853,plain,(
% 2.30/0.69    $false),
% 2.30/0.69    inference(avatar_sat_refutation,[],[f690,f771,f1850])).
% 2.30/0.69  fof(f1850,plain,(
% 2.30/0.69    ~spl9_17 | ~spl9_18),
% 2.30/0.69    inference(avatar_contradiction_clause,[],[f1849])).
% 2.30/0.69  fof(f1849,plain,(
% 2.30/0.69    $false | (~spl9_17 | ~spl9_18)),
% 2.30/0.69    inference(subsumption_resolution,[],[f1848,f176])).
% 2.30/0.69  fof(f176,plain,(
% 2.30/0.69    l1_pre_topc(sK4)),
% 2.30/0.69    inference(subsumption_resolution,[],[f172,f62])).
% 2.30/0.69  fof(f62,plain,(
% 2.30/0.69    l1_pre_topc(sK2)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f51,plain,(
% 2.30/0.69    ((((((~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.30/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f50,f49,f48,f47,f46,f45,f44])).
% 2.30/0.69  fof(f44,plain,(
% 2.30/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f45,plain,(
% 2.30/0.69    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f46,plain,(
% 2.30/0.69    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f47,plain,(
% 2.30/0.69    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f48,plain,(
% 2.30/0.69    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f49,plain,(
% 2.30/0.69    ? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f50,plain,(
% 2.30/0.69    ? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 2.30/0.69    introduced(choice_axiom,[])).
% 2.30/0.69  fof(f19,plain,(
% 2.30/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.30/0.69    inference(flattening,[],[f18])).
% 2.30/0.69  fof(f18,plain,(
% 2.30/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f17])).
% 2.30/0.69  fof(f17,negated_conjecture,(
% 2.30/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.30/0.69    inference(negated_conjecture,[],[f16])).
% 2.30/0.69  fof(f16,conjecture,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 2.30/0.69  fof(f172,plain,(
% 2.30/0.69    l1_pre_topc(sK4) | ~l1_pre_topc(sK2)),
% 2.30/0.69    inference(resolution,[],[f82,f67])).
% 2.30/0.69  fof(f67,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK2)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f82,plain,(
% 2.30/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f23])).
% 2.30/0.69  fof(f23,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f5])).
% 2.30/0.69  fof(f5,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.30/0.69  fof(f1848,plain,(
% 2.30/0.69    ~l1_pre_topc(sK4) | (~spl9_17 | ~spl9_18)),
% 2.30/0.69    inference(subsumption_resolution,[],[f1846,f679])).
% 2.30/0.69  fof(f679,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK4) | ~spl9_18),
% 2.30/0.69    inference(avatar_component_clause,[],[f678])).
% 2.30/0.69  fof(f678,plain,(
% 2.30/0.69    spl9_18 <=> m1_pre_topc(sK4,sK4)),
% 2.30/0.69    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 2.30/0.69  fof(f1846,plain,(
% 2.30/0.69    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | ~spl9_17),
% 2.30/0.69    inference(resolution,[],[f1845,f226])).
% 2.30/0.69  fof(f226,plain,(
% 2.30/0.69    ( ! [X0] : (m1_pre_topc(sK5,X0) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(superposition,[],[f86,f73])).
% 2.30/0.69  fof(f73,plain,(
% 2.30/0.69    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f86,plain,(
% 2.30/0.69    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f26])).
% 2.30/0.69  fof(f26,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f8])).
% 2.30/0.69  fof(f8,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 2.30/0.69  fof(f1845,plain,(
% 2.30/0.69    ~m1_pre_topc(sK5,sK4) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1844,f66])).
% 2.30/0.69  fof(f66,plain,(
% 2.30/0.69    ~v2_struct_0(sK4)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1844,plain,(
% 2.30/0.69    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1843,f193])).
% 2.30/0.69  fof(f193,plain,(
% 2.30/0.69    v2_pre_topc(sK4)),
% 2.30/0.69    inference(subsumption_resolution,[],[f192,f61])).
% 2.30/0.69  fof(f61,plain,(
% 2.30/0.69    v2_pre_topc(sK2)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f192,plain,(
% 2.30/0.69    v2_pre_topc(sK4) | ~v2_pre_topc(sK2)),
% 2.30/0.69    inference(subsumption_resolution,[],[f188,f62])).
% 2.30/0.69  fof(f188,plain,(
% 2.30/0.69    v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 2.30/0.69    inference(resolution,[],[f93,f67])).
% 2.30/0.69  fof(f93,plain,(
% 2.30/0.69    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f36])).
% 2.30/0.69  fof(f36,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.69    inference(flattening,[],[f35])).
% 2.30/0.69  fof(f35,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f2])).
% 2.30/0.69  fof(f2,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.30/0.69  fof(f1843,plain,(
% 2.30/0.69    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1842,f176])).
% 2.30/0.69  fof(f1842,plain,(
% 2.30/0.69    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | ~spl9_17),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f1841])).
% 2.30/0.69  fof(f1841,plain,(
% 2.30/0.69    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK4) | ~spl9_17),
% 2.30/0.69    inference(resolution,[],[f1840,f1080])).
% 2.30/0.69  fof(f1080,plain,(
% 2.30/0.69    ( ! [X0] : (~v1_tsep_1(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,X0)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1079,f63])).
% 2.30/0.69  fof(f63,plain,(
% 2.30/0.69    ~v2_struct_0(sK3)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1079,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1078,f64])).
% 2.30/0.69  fof(f64,plain,(
% 2.30/0.69    v2_pre_topc(sK3)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1078,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1077,f65])).
% 2.30/0.69  fof(f65,plain,(
% 2.30/0.69    l1_pre_topc(sK3)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1077,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1076,f66])).
% 2.30/0.69  fof(f1076,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1075,f68])).
% 2.30/0.69  fof(f68,plain,(
% 2.30/0.69    ~v2_struct_0(sK5)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1075,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1074,f70])).
% 2.30/0.69  fof(f70,plain,(
% 2.30/0.69    v1_funct_1(sK6)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1074,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1073,f71])).
% 2.30/0.69  fof(f71,plain,(
% 2.30/0.69    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1073,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1072,f72])).
% 2.30/0.69  fof(f72,plain,(
% 2.30/0.69    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1072,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1071,f655])).
% 2.30/0.69  fof(f655,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5) | ~spl9_17),
% 2.30/0.69    inference(avatar_component_clause,[],[f654])).
% 2.30/0.69  fof(f654,plain,(
% 2.30/0.69    spl9_17 <=> m1_pre_topc(sK4,sK5)),
% 2.30/0.69    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.30/0.69  fof(f1071,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1070,f74])).
% 2.30/0.69  fof(f74,plain,(
% 2.30/0.69    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1070,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1069,f113])).
% 2.30/0.69  fof(f113,plain,(
% 2.30/0.69    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.30/0.69    inference(forward_demodulation,[],[f75,f76])).
% 2.30/0.69  fof(f76,plain,(
% 2.30/0.69    sK7 = sK8),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f75,plain,(
% 2.30/0.69    m1_subset_1(sK8,u1_struct_0(sK4))),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1069,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1068,f78])).
% 2.30/0.69  fof(f78,plain,(
% 2.30/0.69    ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1068,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f1051])).
% 2.30/0.69  fof(f1051,plain,(
% 2.30/0.69    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl9_17),
% 2.30/0.69    inference(resolution,[],[f1039,f602])).
% 2.30/0.69  fof(f602,plain,(
% 2.30/0.69    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f112,f94])).
% 2.30/0.69  fof(f94,plain,(
% 2.30/0.69    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f38])).
% 2.30/0.69  fof(f38,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.69    inference(flattening,[],[f37])).
% 2.30/0.69  fof(f37,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f14])).
% 2.30/0.69  fof(f14,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.30/0.69  fof(f112,plain,(
% 2.30/0.69    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f106])).
% 2.30/0.69  fof(f106,plain,(
% 2.30/0.69    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(equality_resolution,[],[f91])).
% 2.30/0.69  fof(f91,plain,(
% 2.30/0.69    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f53])).
% 2.30/0.69  fof(f53,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.69    inference(nnf_transformation,[],[f32])).
% 2.30/0.69  fof(f32,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.69    inference(flattening,[],[f31])).
% 2.30/0.69  fof(f31,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f15])).
% 2.30/0.69  fof(f15,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).
% 2.30/0.69  fof(f1039,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1038,f60])).
% 2.30/0.69  fof(f60,plain,(
% 2.30/0.69    ~v2_struct_0(sK2)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1038,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1037,f61])).
% 2.30/0.69  fof(f1037,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1036,f62])).
% 2.30/0.69  fof(f1036,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1035,f69])).
% 2.30/0.69  fof(f69,plain,(
% 2.30/0.69    m1_pre_topc(sK5,sK2)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1035,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1034,f63])).
% 2.30/0.69  fof(f1034,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1033,f64])).
% 2.30/0.69  fof(f1033,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1032,f65])).
% 2.30/0.69  fof(f1032,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1031,f70])).
% 2.30/0.69  fof(f1031,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1030,f71])).
% 2.30/0.69  fof(f1030,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f1029,f72])).
% 2.30/0.69  fof(f1029,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_17),
% 2.30/0.69    inference(subsumption_resolution,[],[f951,f655])).
% 2.30/0.69  fof(f951,plain,(
% 2.30/0.69    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 2.30/0.69    inference(superposition,[],[f114,f522])).
% 2.30/0.69  fof(f522,plain,(
% 2.30/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f521])).
% 2.30/0.69  fof(f521,plain,(
% 2.30/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.30/0.69    inference(superposition,[],[f375,f375])).
% 2.30/0.69  fof(f375,plain,(
% 2.30/0.69    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f89,f94])).
% 2.30/0.69  fof(f89,plain,(
% 2.30/0.69    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f30])).
% 2.30/0.69  fof(f30,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.30/0.69    inference(flattening,[],[f29])).
% 2.30/0.69  fof(f29,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f7])).
% 2.30/0.69  fof(f7,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.30/0.69  fof(f114,plain,(
% 2.30/0.69    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)),
% 2.30/0.69    inference(forward_demodulation,[],[f77,f76])).
% 2.30/0.69  fof(f77,plain,(
% 2.30/0.69    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 2.30/0.69    inference(cnf_transformation,[],[f51])).
% 2.30/0.69  fof(f1840,plain,(
% 2.30/0.69    ( ! [X1] : (v1_tsep_1(X1,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.30/0.69    inference(resolution,[],[f1838,f97])).
% 2.30/0.69  fof(f97,plain,(
% 2.30/0.69    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tsep_1(X1,X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f57])).
% 2.30/0.69  fof(f57,plain,(
% 2.30/0.69    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 2.30/0.69    inference(flattening,[],[f56])).
% 2.30/0.69  fof(f56,plain,(
% 2.30/0.69    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 2.30/0.69    inference(nnf_transformation,[],[f41])).
% 2.30/0.69  fof(f41,plain,(
% 2.30/0.69    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 2.30/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.30/0.69  fof(f1838,plain,(
% 2.30/0.69    ( ! [X0] : (sP0(X0,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f1837,f81])).
% 2.30/0.69  fof(f81,plain,(
% 2.30/0.69    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f22])).
% 2.30/0.69  fof(f22,plain,(
% 2.30/0.69    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f12])).
% 2.30/0.69  fof(f12,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.30/0.69  fof(f1837,plain,(
% 2.30/0.69    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X0,X0) | sP0(X0,X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f1836,f80])).
% 2.30/0.69  fof(f80,plain,(
% 2.30/0.69    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f21])).
% 2.30/0.69  fof(f21,plain,(
% 2.30/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f4])).
% 2.30/0.69  fof(f4,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.30/0.69  fof(f1836,plain,(
% 2.30/0.69    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X0,X0) | sP0(X0,X0) | ~l1_struct_0(X0)) )),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f1833])).
% 2.30/0.69  fof(f1833,plain,(
% 2.30/0.69    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X0,X0) | sP0(X0,X0) | ~l1_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(resolution,[],[f371,f92])).
% 2.30/0.69  fof(f92,plain,(
% 2.30/0.69    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f34])).
% 2.30/0.69  fof(f34,plain,(
% 2.30/0.69    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.69    inference(flattening,[],[f33])).
% 2.30/0.69  fof(f33,plain,(
% 2.30/0.69    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f6])).
% 2.30/0.69  fof(f6,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.30/0.69  fof(f371,plain,(
% 2.30/0.69    ( ! [X0,X1] : (~v3_pre_topc(k2_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | sP0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.30/0.69    inference(superposition,[],[f284,f79])).
% 2.30/0.69  fof(f79,plain,(
% 2.30/0.69    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f20])).
% 2.30/0.69  fof(f20,plain,(
% 2.30/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f3])).
% 2.30/0.69  fof(f3,axiom,(
% 2.30/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.30/0.69  fof(f284,plain,(
% 2.30/0.69    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | sP0(X1,X0)) )),
% 2.30/0.69    inference(resolution,[],[f272,f96])).
% 2.30/0.69  fof(f96,plain,(
% 2.30/0.69    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_pre_topc(X1,X0) | sP0(X0,X2)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f55])).
% 2.30/0.69  fof(f55,plain,(
% 2.30/0.69    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 2.30/0.69    inference(rectify,[],[f54])).
% 2.30/0.69  fof(f54,plain,(
% 2.30/0.69    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 2.30/0.69    inference(nnf_transformation,[],[f42])).
% 2.30/0.69  fof(f42,plain,(
% 2.30/0.69    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 2.30/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.30/0.69  fof(f272,plain,(
% 2.30/0.69    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f108,f84])).
% 2.30/0.69  fof(f84,plain,(
% 2.30/0.69    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f25])).
% 2.30/0.69  fof(f25,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f11])).
% 2.30/0.69  fof(f11,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.30/0.69  fof(f108,plain,(
% 2.30/0.69    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(equality_resolution,[],[f100])).
% 2.30/0.69  fof(f100,plain,(
% 2.30/0.69    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f43])).
% 2.30/0.69  fof(f43,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.69    inference(definition_folding,[],[f40,f42,f41])).
% 2.30/0.69  fof(f40,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.30/0.69    inference(flattening,[],[f39])).
% 2.30/0.69  fof(f39,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.30/0.69    inference(ennf_transformation,[],[f10])).
% 2.30/0.69  fof(f10,axiom,(
% 2.30/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 2.30/0.69  fof(f771,plain,(
% 2.30/0.69    spl9_17),
% 2.30/0.69    inference(avatar_split_clause,[],[f770,f654])).
% 2.30/0.69  fof(f770,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f769,f177])).
% 2.30/0.69  fof(f177,plain,(
% 2.30/0.69    l1_pre_topc(sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f173,f62])).
% 2.30/0.69  fof(f173,plain,(
% 2.30/0.69    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 2.30/0.69    inference(resolution,[],[f82,f69])).
% 2.30/0.69  fof(f769,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5) | ~l1_pre_topc(sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f768,f195])).
% 2.30/0.69  fof(f195,plain,(
% 2.30/0.69    v2_pre_topc(sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f194,f61])).
% 2.30/0.69  fof(f194,plain,(
% 2.30/0.69    v2_pre_topc(sK5) | ~v2_pre_topc(sK2)),
% 2.30/0.69    inference(subsumption_resolution,[],[f189,f62])).
% 2.30/0.69  fof(f189,plain,(
% 2.30/0.69    v2_pre_topc(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 2.30/0.69    inference(resolution,[],[f93,f69])).
% 2.30/0.69  fof(f768,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f767,f193])).
% 2.30/0.69  fof(f767,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5) | ~v2_pre_topc(sK4) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK5)),
% 2.30/0.69    inference(subsumption_resolution,[],[f753,f176])).
% 2.30/0.69  fof(f753,plain,(
% 2.30/0.69    m1_pre_topc(sK4,sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~v2_pre_topc(sK5) | ~l1_pre_topc(sK5)),
% 2.30/0.69    inference(superposition,[],[f339,f73])).
% 2.30/0.69  fof(f339,plain,(
% 2.30/0.69    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 2.30/0.69    inference(duplicate_literal_removal,[],[f332])).
% 2.30/0.69  fof(f332,plain,(
% 2.30/0.69    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 2.30/0.69    inference(resolution,[],[f325,f81])).
% 2.30/0.69  fof(f325,plain,(
% 2.30/0.69    ( ! [X2,X0] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(subsumption_resolution,[],[f105,f82])).
% 2.30/0.69  fof(f105,plain,(
% 2.30/0.69    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(equality_resolution,[],[f87])).
% 2.30/0.69  fof(f87,plain,(
% 2.30/0.69    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.30/0.69    inference(cnf_transformation,[],[f52])).
% 2.30/0.69  fof(f52,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(nnf_transformation,[],[f28])).
% 2.30/0.69  fof(f28,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(flattening,[],[f27])).
% 2.30/0.69  fof(f27,plain,(
% 2.30/0.69    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 2.30/0.69    inference(ennf_transformation,[],[f9])).
% 2.30/0.69  fof(f9,axiom,(
% 2.30/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 2.30/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 2.30/0.69  fof(f690,plain,(
% 2.30/0.69    spl9_18),
% 2.30/0.69    inference(avatar_contradiction_clause,[],[f689])).
% 2.30/0.69  fof(f689,plain,(
% 2.30/0.69    $false | spl9_18),
% 2.30/0.69    inference(subsumption_resolution,[],[f686,f176])).
% 2.30/0.69  fof(f686,plain,(
% 2.30/0.69    ~l1_pre_topc(sK4) | spl9_18),
% 2.30/0.69    inference(resolution,[],[f680,f81])).
% 2.30/0.69  fof(f680,plain,(
% 2.30/0.69    ~m1_pre_topc(sK4,sK4) | spl9_18),
% 2.30/0.69    inference(avatar_component_clause,[],[f678])).
% 2.30/0.69  % SZS output end Proof for theBenchmark
% 2.30/0.69  % (1476)------------------------------
% 2.30/0.69  % (1476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.69  % (1476)Termination reason: Refutation
% 2.30/0.69  
% 2.30/0.69  % (1476)Memory used [KB]: 7291
% 2.30/0.69  % (1476)Time elapsed: 0.268 s
% 2.30/0.69  % (1476)------------------------------
% 2.30/0.69  % (1476)------------------------------
% 2.30/0.69  % (1470)Success in time 0.334 s
%------------------------------------------------------------------------------
