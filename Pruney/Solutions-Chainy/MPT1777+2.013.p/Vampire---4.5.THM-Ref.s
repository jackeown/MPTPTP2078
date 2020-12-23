%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:03 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  176 (2811 expanded)
%              Number of leaves         :   24 (1440 expanded)
%              Depth                    :   30
%              Number of atoms          : 1021 (43812 expanded)
%              Number of equality atoms :  105 (5916 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1859,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1858,f120])).

fof(f120,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f116,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f116,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f114,f65])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f52,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK1,X4,X5)
                          & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK1,X4,X5)
                        & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK1,X4,X5)
                      & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK1,X4,X5)
                    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK3,sK1,X4,X5)
                  & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK3,sK1,X4,X5)
                & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK3,sK1,sK4,X5)
              & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK3,sK1,sK4,X5)
            & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
          & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
        & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6)
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
      & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f84,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1858,plain,(
    ~ m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f1854,f160])).

fof(f160,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2) ) ),
    inference(forward_demodulation,[],[f159,f71])).

fof(f71,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(subsumption_resolution,[],[f155,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f116,f84])).

fof(f155,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f82,f116])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f1854,plain,(
    ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f1852,f545])).

fof(f545,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f180,f321])).

fof(f321,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK3) ),
    inference(superposition,[],[f240,f287])).

fof(f287,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(superposition,[],[f245,f222])).

fof(f222,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f221,f117])).

fof(f117,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f114,f67])).

fof(f67,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f221,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f213,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f213,plain,(
    v1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f211,f116])).

fof(f211,plain,
    ( v1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f131,f71])).

fof(f131,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f245,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK3
      | u1_struct_0(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f244,f116])).

fof(f244,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2) = X0
      | g1_pre_topc(X0,X1) != sK3
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f189,f80])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | u1_struct_0(sK2) = X0
      | g1_pre_topc(X0,X1) != sK3 ) ),
    inference(superposition,[],[f98,f71])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f240,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(superposition,[],[f172,f208])).

fof(f208,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f113,f117])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f77,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f172,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f169,f117])).

fof(f169,plain,
    ( ~ l1_pre_topc(sK3)
    | v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(resolution,[],[f141,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f141,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f129,f67])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f127,f60])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f180,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f176,f117])).

fof(f176,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),sK3)
      | ~ m1_pre_topc(X3,sK3)
      | ~ l1_pre_topc(sK3)
      | v1_tsep_1(X3,sK3) ) ),
    inference(resolution,[],[f109,f141])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f103,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f1852,plain,(
    ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1851,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f1851,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1850,f141])).

fof(f1850,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1849,f117])).

fof(f1849,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1848,f126])).

fof(f126,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f117,f79])).

fof(f1848,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1847,f133])).

% (11035)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f133,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(superposition,[],[f75,f74])).

fof(f74,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f1847,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f1117,f1566])).

fof(f1566,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(forward_demodulation,[],[f1565,f1004])).

fof(f1004,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK3,sK4) ),
    inference(superposition,[],[f966,f559])).

fof(f559,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f557,f287])).

fof(f557,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f430,f126])).

fof(f430,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X2)) ) ),
    inference(forward_demodulation,[],[f429,f287])).

fof(f429,plain,(
    ! [X2] :
      ( k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f428,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f428,plain,(
    ! [X2] :
      ( k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f427,f59])).

fof(f427,plain,(
    ! [X2] :
      ( k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f418,f60])).

fof(f418,plain,(
    ! [X2] :
      ( k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f253,f67])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f252,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f251,f62])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f250,f63])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f197,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
      | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f196,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
      | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_pre_topc(X1,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f87,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f966,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f558,f120])).

fof(f558,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f430,f160])).

fof(f1565,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(forward_demodulation,[],[f1563,f559])).

fof(f1563,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(resolution,[],[f963,f120])).

fof(f963,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK4) ) ),
    inference(resolution,[],[f438,f160])).

fof(f438,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X4)) ) ),
    inference(forward_demodulation,[],[f437,f287])).

fof(f437,plain,(
    ! [X4] :
      ( k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,sK3) ) ),
    inference(subsumption_resolution,[],[f436,f66])).

fof(f436,plain,(
    ! [X4] :
      ( k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f435,f141])).

fof(f435,plain,(
    ! [X4] :
      ( k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f420,f117])).

fof(f420,plain,(
    ! [X4] :
      ( k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X4,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f253,f126])).

fof(f1117,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
      | ~ v1_tsep_1(sK2,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f1116,f120])).

fof(f1116,plain,(
    ! [X0] :
      ( ~ v1_tsep_1(sK2,X0)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK2,sK2) ) ),
    inference(resolution,[],[f767,f160])).

fof(f767,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,sK3)
      | ~ v1_tsep_1(sK2,X1)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f763,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f763,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK2,sK3)
      | ~ v1_tsep_1(sK2,X1)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f466,f108])).

fof(f108,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f73,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f466,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ v1_tsep_1(X0,X1)
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f464,f76])).

fof(f76,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f464,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ v1_tsep_1(X0,X1)
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
      | r1_tmap_1(sK3,sK1,sK4,sK5)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f269,f72])).

fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f268,f61])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f267,f62])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f266,f63])).

fof(f266,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f265,f66])).

fof(f265,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK3)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f264,f69])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ v1_tsep_1(X1,X2)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK3)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f203,f70])).

fof(f203,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X0,X3)
      | ~ v1_tsep_1(X0,X2)
      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,sK4,X4)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f202,f92])).

fof(f202,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_pre_topc(X0,X2)
      | ~ v1_tsep_1(X0,X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,sK4,X4)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f107,f68])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | r1_tmap_1(X3,X0,X4,X6)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (11021)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (11029)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (11019)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (11016)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (11012)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (11012)Refutation not found, incomplete strategy% (11012)------------------------------
% 0.21/0.49  % (11012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11014)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (11019)Refutation not found, incomplete strategy% (11019)------------------------------
% 0.21/0.50  % (11019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11019)Memory used [KB]: 1918
% 0.21/0.50  % (11019)Time elapsed: 0.080 s
% 0.21/0.50  % (11019)------------------------------
% 0.21/0.50  % (11019)------------------------------
% 0.21/0.50  % (11012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11012)Memory used [KB]: 10874
% 0.21/0.50  % (11012)Time elapsed: 0.088 s
% 0.21/0.50  % (11012)------------------------------
% 0.21/0.50  % (11012)------------------------------
% 0.21/0.50  % (11030)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (11027)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (11028)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (11015)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (11032)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (11024)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (11034)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (11013)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11033)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (11022)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (11026)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (11017)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (11020)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.33/0.52  % (11023)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.33/0.52  % (11017)Refutation not found, incomplete strategy% (11017)------------------------------
% 1.33/0.52  % (11017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.52  % (11017)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.52  
% 1.33/0.52  % (11017)Memory used [KB]: 6268
% 1.33/0.52  % (11017)Time elapsed: 0.120 s
% 1.33/0.52  % (11017)------------------------------
% 1.33/0.52  % (11017)------------------------------
% 1.33/0.53  % (11025)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (11031)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.33/0.53  % (11018)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.33/0.53  % (11036)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.33/0.54  % (11028)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f1859,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(subsumption_resolution,[],[f1858,f120])).
% 1.33/0.54  fof(f120,plain,(
% 1.33/0.54    m1_pre_topc(sK2,sK2)),
% 1.33/0.54    inference(resolution,[],[f116,f79])).
% 1.33/0.54  fof(f79,plain,(
% 1.33/0.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.33/0.54  fof(f116,plain,(
% 1.33/0.54    l1_pre_topc(sK2)),
% 1.33/0.54    inference(resolution,[],[f114,f65])).
% 1.33/0.54  fof(f65,plain,(
% 1.33/0.54    m1_pre_topc(sK2,sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f52,f51,f50,f49,f48,f47,f46])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,negated_conjecture,(
% 1.33/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.33/0.54    inference(negated_conjecture,[],[f18])).
% 1.33/0.54  fof(f18,conjecture,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.33/0.54  fof(f114,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.33/0.54    inference(resolution,[],[f84,f60])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    l1_pre_topc(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f84,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.33/0.54  fof(f1858,plain,(
% 1.33/0.54    ~m1_pre_topc(sK2,sK2)),
% 1.33/0.54    inference(resolution,[],[f1854,f160])).
% 1.33/0.54  fof(f160,plain,(
% 1.33/0.54    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2)) )),
% 1.33/0.54    inference(forward_demodulation,[],[f159,f71])).
% 1.33/0.54  fof(f71,plain,(
% 1.33/0.54    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f159,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f155,f119])).
% 1.33/0.54  fof(f119,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 1.33/0.54    inference(resolution,[],[f116,f84])).
% 1.33/0.54  fof(f155,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK2) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(X2)) )),
% 1.33/0.54    inference(resolution,[],[f82,f116])).
% 1.33/0.54  fof(f82,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f54])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f28])).
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.33/0.54  fof(f1854,plain,(
% 1.33/0.54    ~m1_pre_topc(sK2,sK3)),
% 1.33/0.54    inference(resolution,[],[f1852,f545])).
% 1.33/0.54  fof(f545,plain,(
% 1.33/0.54    v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3)),
% 1.33/0.54    inference(resolution,[],[f180,f321])).
% 1.33/0.54  fof(f321,plain,(
% 1.33/0.54    v3_pre_topc(u1_struct_0(sK2),sK3)),
% 1.33/0.54    inference(superposition,[],[f240,f287])).
% 1.33/0.54  fof(f287,plain,(
% 1.33/0.54    u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f284])).
% 1.33/0.54  fof(f284,plain,(
% 1.33/0.54    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3)),
% 1.33/0.54    inference(superposition,[],[f245,f222])).
% 1.33/0.54  fof(f222,plain,(
% 1.33/0.54    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 1.33/0.54    inference(subsumption_resolution,[],[f221,f117])).
% 1.33/0.54  fof(f117,plain,(
% 1.33/0.54    l1_pre_topc(sK3)),
% 1.33/0.54    inference(resolution,[],[f114,f67])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    m1_pre_topc(sK3,sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f221,plain,(
% 1.33/0.54    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3)),
% 1.33/0.54    inference(resolution,[],[f213,f81])).
% 1.33/0.54  fof(f81,plain,(
% 1.33/0.54    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f27])).
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.33/0.54  fof(f213,plain,(
% 1.33/0.54    v1_pre_topc(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f211,f116])).
% 1.33/0.54  fof(f211,plain,(
% 1.33/0.54    v1_pre_topc(sK3) | ~l1_pre_topc(sK2)),
% 1.33/0.54    inference(superposition,[],[f131,f71])).
% 1.33/0.54  fof(f131,plain,(
% 1.33/0.54    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(resolution,[],[f96,f80])).
% 1.33/0.54  fof(f80,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.33/0.54  fof(f96,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f44])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.33/0.54  fof(f245,plain,(
% 1.33/0.54    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK3 | u1_struct_0(sK2) = X0) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f244,f116])).
% 1.33/0.54  fof(f244,plain,(
% 1.33/0.54    ( ! [X0,X1] : (u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3 | ~l1_pre_topc(sK2)) )),
% 1.33/0.54    inference(resolution,[],[f189,f80])).
% 1.33/0.54  fof(f189,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | u1_struct_0(sK2) = X0 | g1_pre_topc(X0,X1) != sK3) )),
% 1.33/0.54    inference(superposition,[],[f98,f71])).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f45])).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.33/0.54  fof(f240,plain,(
% 1.33/0.54    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 1.33/0.54    inference(superposition,[],[f172,f208])).
% 1.33/0.54  fof(f208,plain,(
% 1.33/0.54    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.33/0.54    inference(resolution,[],[f113,f117])).
% 1.33/0.54  fof(f113,plain,(
% 1.33/0.54    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.33/0.54    inference(resolution,[],[f77,f78])).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.33/0.54  fof(f172,plain,(
% 1.33/0.54    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f169,f117])).
% 1.33/0.54  fof(f169,plain,(
% 1.33/0.54    ~l1_pre_topc(sK3) | v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.33/0.54    inference(resolution,[],[f141,f90])).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f37])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f36])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.33/0.54  fof(f141,plain,(
% 1.33/0.54    v2_pre_topc(sK3)),
% 1.33/0.54    inference(resolution,[],[f129,f67])).
% 1.33/0.54  fof(f129,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f127,f60])).
% 1.33/0.54  fof(f127,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) )),
% 1.33/0.54    inference(resolution,[],[f91,f59])).
% 1.33/0.54  fof(f59,plain,(
% 1.33/0.54    v2_pre_topc(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f91,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f38])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.33/0.54  fof(f180,plain,(
% 1.33/0.54    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | v1_tsep_1(X3,sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f176,f117])).
% 1.33/0.54  fof(f176,plain,(
% 1.33/0.54    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),sK3) | ~m1_pre_topc(X3,sK3) | ~l1_pre_topc(sK3) | v1_tsep_1(X3,sK3)) )),
% 1.33/0.54    inference(resolution,[],[f109,f141])).
% 1.33/0.54  fof(f109,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f103,f85])).
% 1.33/0.54  fof(f85,plain,(
% 1.33/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f14])).
% 1.33/0.54  fof(f14,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.33/0.54  fof(f103,plain,(
% 1.33/0.54    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/0.54    inference(equality_resolution,[],[f94])).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f56])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.33/0.54  fof(f1852,plain,(
% 1.33/0.54    ~v1_tsep_1(sK2,sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f1851,f66])).
% 1.33/0.54  fof(f66,plain,(
% 1.33/0.54    ~v2_struct_0(sK3)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f1851,plain,(
% 1.33/0.54    ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f1850,f141])).
% 1.33/0.54  fof(f1850,plain,(
% 1.33/0.54    ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f1849,f117])).
% 1.33/0.54  fof(f1849,plain,(
% 1.33/0.54    ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f1848,f126])).
% 1.33/0.54  fof(f126,plain,(
% 1.33/0.54    m1_pre_topc(sK3,sK3)),
% 1.33/0.54    inference(resolution,[],[f117,f79])).
% 1.33/0.54  fof(f1848,plain,(
% 1.33/0.54    ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.33/0.54    inference(subsumption_resolution,[],[f1847,f133])).
% 1.33/0.54  % (11035)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.33/0.54  fof(f133,plain,(
% 1.33/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.33/0.54    inference(superposition,[],[f75,f74])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    sK5 = sK6),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f1847,plain,(
% 1.33/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.33/0.54    inference(superposition,[],[f1117,f1566])).
% 1.33/0.54  fof(f1566,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.33/0.54    inference(forward_demodulation,[],[f1565,f1004])).
% 1.33/0.54  fof(f1004,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK0,sK1,sK3,sK3,sK4)),
% 1.33/0.54    inference(superposition,[],[f966,f559])).
% 1.33/0.54  fof(f559,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.33/0.54    inference(forward_demodulation,[],[f557,f287])).
% 1.33/0.54  fof(f557,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 1.33/0.54    inference(resolution,[],[f430,f126])).
% 1.33/0.54  fof(f430,plain,(
% 1.33/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK3) | k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X2))) )),
% 1.33/0.54    inference(forward_demodulation,[],[f429,f287])).
% 1.33/0.54  fof(f429,plain,(
% 1.33/0.54    ( ! [X2] : (k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f428,f58])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ~v2_struct_0(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f428,plain,(
% 1.33/0.54    ( ! [X2] : (k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK3) | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f427,f59])).
% 1.33/0.54  fof(f427,plain,(
% 1.33/0.54    ( ! [X2] : (k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f418,f60])).
% 1.33/0.54  fof(f418,plain,(
% 1.33/0.54    ( ! [X2] : (k3_tmap_1(sK0,sK1,sK3,X2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.33/0.54    inference(resolution,[],[f253,f67])).
% 1.33/0.54  fof(f253,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f252,f61])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    ~v2_struct_0(sK1)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f252,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f251,f62])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    v2_pre_topc(sK1)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f251,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f250,f63])).
% 1.33/0.54  fof(f63,plain,(
% 1.33/0.54    l1_pre_topc(sK1)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f250,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f249,f69])).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f249,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | k3_tmap_1(X1,sK1,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(resolution,[],[f197,f70])).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f197,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f196,f92])).
% 1.33/0.54  fof(f92,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X2,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f41])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f40])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.33/0.54  fof(f196,plain,(
% 1.33/0.54    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X0,X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.33/0.54    inference(resolution,[],[f87,f68])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    v1_funct_1(sK4)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f87,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f33])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.33/0.54  fof(f966,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.33/0.54    inference(resolution,[],[f558,f120])).
% 1.33/0.54  fof(f558,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 1.33/0.54    inference(resolution,[],[f430,f160])).
% 1.33/0.54  fof(f1565,plain,(
% 1.33/0.54    k3_tmap_1(sK0,sK1,sK3,sK3,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.33/0.54    inference(forward_demodulation,[],[f1563,f559])).
% 1.33/0.54  fof(f1563,plain,(
% 1.33/0.54    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.33/0.54    inference(resolution,[],[f963,f120])).
% 1.33/0.54  fof(f963,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK3,sK1,sK3,X0,sK4)) )),
% 1.33/0.54    inference(resolution,[],[f438,f160])).
% 1.33/0.54  fof(f438,plain,(
% 1.33/0.54    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X4))) )),
% 1.33/0.54    inference(forward_demodulation,[],[f437,f287])).
% 1.33/0.54  fof(f437,plain,(
% 1.33/0.54    ( ! [X4] : (k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X4,sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f436,f66])).
% 1.33/0.54  fof(f436,plain,(
% 1.33/0.54    ( ! [X4] : (k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X4,sK3) | v2_struct_0(sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f435,f141])).
% 1.33/0.54  fof(f435,plain,(
% 1.33/0.54    ( ! [X4] : (k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f420,f117])).
% 1.33/0.54  fof(f420,plain,(
% 1.33/0.54    ( ! [X4] : (k3_tmap_1(sK3,sK1,sK3,X4,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.33/0.54    inference(resolution,[],[f253,f126])).
% 1.33/0.54  fof(f1117,plain,(
% 1.33/0.54    ( ! [X0] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f1116,f120])).
% 1.33/0.54  fof(f1116,plain,(
% 1.33/0.54    ( ! [X0] : (~v1_tsep_1(sK2,X0) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X0,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK2,sK2)) )),
% 1.33/0.54    inference(resolution,[],[f767,f160])).
% 1.33/0.54  fof(f767,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,X1) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f763,f64])).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ~v2_struct_0(sK2)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f763,plain,(
% 1.33/0.54    ( ! [X1] : (~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,X1) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X1,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(resolution,[],[f466,f108])).
% 1.33/0.54  fof(f108,plain,(
% 1.33/0.54    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.33/0.54    inference(forward_demodulation,[],[f73,f74])).
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f466,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f464,f76])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f464,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(resolution,[],[f269,f72])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.33/0.54    inference(cnf_transformation,[],[f53])).
% 1.33/0.54  fof(f269,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f268,f61])).
% 1.33/0.54  fof(f268,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f267,f62])).
% 1.33/0.54  fof(f267,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f266,f63])).
% 1.33/0.54  fof(f266,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f265,f66])).
% 1.33/0.54  fof(f265,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f264,f69])).
% 1.33/0.54  fof(f264,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,X2) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.33/0.54    inference(resolution,[],[f203,f70])).
% 1.33/0.54  fof(f203,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X0,X3) | ~v1_tsep_1(X0,X2) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(subsumption_resolution,[],[f202,f92])).
% 1.33/0.54  fof(f202,plain,(
% 1.33/0.54    ( ! [X4,X2,X0,X3,X1] : (~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X0,X2) | ~v1_tsep_1(X0,X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.33/0.54    inference(resolution,[],[f107,f68])).
% 1.33/0.54  fof(f107,plain,(
% 1.33/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | r1_tmap_1(X3,X0,X4,X6) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(duplicate_literal_removal,[],[f100])).
% 1.33/0.54  fof(f100,plain,(
% 1.33/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(equality_resolution,[],[f89])).
% 1.33/0.54  fof(f89,plain,(
% 1.33/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f55])).
% 1.33/0.54  fof(f55,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f34])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,axiom,(
% 1.33/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.33/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (11028)------------------------------
% 1.33/0.54  % (11028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (11028)Termination reason: Refutation
% 1.33/0.54  
% 1.48/0.54  % (11028)Memory used [KB]: 2174
% 1.48/0.54  % (11028)Time elapsed: 0.130 s
% 1.48/0.54  % (11028)------------------------------
% 1.48/0.54  % (11028)------------------------------
% 1.48/0.54  % (11011)Success in time 0.186 s
%------------------------------------------------------------------------------
