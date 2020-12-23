%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:07 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  186 (6473 expanded)
%              Number of leaves         :   24 (3144 expanded)
%              Depth                    :   41
%              Number of atoms          :  992 (90427 expanded)
%              Number of equality atoms :   59 (12219 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f444,f108])).

fof(f108,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f49,f48,f47,f46,f45,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f444,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f442,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f442,plain,(
    ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f311,f441])).

fof(f441,plain,(
    v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f440,f98])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f440,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) ),
    inference(resolution,[],[f438,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f438,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f437,f123])).

fof(f123,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f101,f118])).

fof(f118,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f104,f107])).

fof(f107,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f105,f63])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f75,f76])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f101,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f437,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
    | v1_xboole_0(k2_struct_0(sK2))
    | ~ m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(resolution,[],[f436,f395])).

fof(f395,plain,(
    ! [X0] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X0)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f394,f98])).

fof(f394,plain,(
    ! [X0] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X0)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f393,f94])).

fof(f393,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2)))
      | m1_connsp_2(k2_struct_0(sK2),sK3,X2)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X2,k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f392,f307])).

fof(f307,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(backward_demodulation,[],[f119,f306])).

fof(f306,plain,(
    k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f234,f305])).

fof(f305,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f304,f119])).

fof(f304,plain,(
    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f303,f118])).

fof(f303,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f296,f107])).

fof(f296,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f289,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f289,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f288,f108])).

fof(f288,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f287,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f287,plain,
    ( ~ m1_pre_topc(sK3,sK3)
    | m1_pre_topc(sK3,sK2) ),
    inference(forward_demodulation,[],[f286,f122])).

fof(f122,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f69,f118])).

fof(f69,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f50])).

fof(f286,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f283,f107])).

fof(f283,plain,
    ( ~ m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK3,sK2) ),
    inference(superposition,[],[f249,f118])).

fof(f249,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(sK3,X3) ) ),
    inference(resolution,[],[f79,f108])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f234,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(resolution,[],[f232,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f232,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f231,f118])).

fof(f231,plain,(
    r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f230,f119])).

fof(f230,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f224,f108])).

fof(f224,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f217,f81])).

fof(f217,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f216,f122])).

fof(f216,plain,(
    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(forward_demodulation,[],[f212,f118])).

fof(f212,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f193,f107])).

fof(f193,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f78,f77])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f104,f108])).

fof(f392,plain,(
    ! [X2] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X2)
      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X2,k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f391,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f391,plain,(
    ! [X2] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X2)
      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | v2_struct_0(sK3)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X2,k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f390,f141])).

fof(f141,plain,(
    v2_pre_topc(sK3) ),
    inference(resolution,[],[f138,f65])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f136,f58])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f390,plain,(
    ! [X2] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X2)
      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X2,k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f388,f108])).

fof(f388,plain,(
    ! [X2] :
      ( m1_connsp_2(k2_struct_0(sK2),sK3,X2)
      | ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ m1_subset_1(X2,k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f386,f360])).

fof(f360,plain,(
    v3_pre_topc(k2_struct_0(sK2),sK3) ),
    inference(subsumption_resolution,[],[f359,f141])).

fof(f359,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f358,f108])).

fof(f358,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(superposition,[],[f86,f306])).

fof(f86,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f386,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X0,X1)
      | m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(subsumption_resolution,[],[f385,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f95,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X0,X1,X2)
      | ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f83,f89])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f436,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f435,f309])).

fof(f309,plain,(
    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f125,f306])).

fof(f125,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f120,f119])).

fof(f120,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f67,f117])).

fof(f117,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f104,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f435,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5) ) ),
    inference(forward_demodulation,[],[f434,f307])).

fof(f434,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5) ) ),
    inference(forward_demodulation,[],[f433,f117])).

fof(f433,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f432,f308])).

fof(f308,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f124,f306])).

fof(f124,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f121,f119])).

fof(f121,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f68,f117])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f432,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f431,f307])).

fof(f431,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f430,f117])).

fof(f430,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f429,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f429,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f428,f307])).

fof(f428,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f427,f123])).

fof(f427,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f426,f307])).

fof(f426,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f425,f123])).

fof(f425,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f424,f118])).

fof(f424,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK2))
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f423,f118])).

fof(f423,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f422,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f422,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f421,f57])).

fof(f421,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f420,f58])).

fof(f420,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f419,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f419,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f418,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f418,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f417,f61])).

fof(f417,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f416,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f416,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f415,f64])).

fof(f415,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f414,f65])).

fof(f414,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f413,f74])).

fof(f74,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f413,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,sK5)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f412,f217])).

fof(f412,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,sK5)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f411,f100])).

fof(f100,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f73,f72])).

fof(f73,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f411,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
      | ~ m1_connsp_2(X5,X3,X4)
      | ~ r1_tarski(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X0,X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,sK4,X4)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f102,f66])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f96,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f96,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X1,X4,X6)
                                      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X1,X4,X6) ) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
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
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
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
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X1,X4,X6)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f311,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK3) ),
    inference(backward_demodulation,[],[f134,f306])).

fof(f134,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f133,f64])).

fof(f133,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f82,f119])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.52  % (27687)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.20/0.52  % (27700)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.20/0.52  % (27684)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.29/0.53  % (27703)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.29/0.53  % (27695)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.29/0.53  % (27692)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.29/0.53  % (27683)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.29/0.53  % (27689)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.29/0.53  % (27705)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.29/0.53  % (27686)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.29/0.54  % (27688)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.29/0.54  % (27687)Refutation not found, incomplete strategy% (27687)------------------------------
% 1.29/0.54  % (27687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (27687)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (27687)Memory used [KB]: 1791
% 1.29/0.54  % (27687)Time elapsed: 0.100 s
% 1.29/0.54  % (27687)------------------------------
% 1.29/0.54  % (27687)------------------------------
% 1.29/0.54  % (27685)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.29/0.54  % (27691)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.29/0.54  % (27682)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.29/0.54  % (27690)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.29/0.54  % (27694)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.29/0.54  % (27698)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.29/0.54  % (27693)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.29/0.55  % (27701)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.29/0.55  % (27680)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.29/0.55  % (27702)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.29/0.55  % (27697)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.29/0.55  % (27681)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (27704)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.29/0.55  % (27699)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.29/0.55  % (27696)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.29/0.56  % (27683)Refutation found. Thanks to Tanya!
% 1.29/0.56  % SZS status Theorem for theBenchmark
% 1.29/0.56  % SZS output start Proof for theBenchmark
% 1.29/0.56  fof(f445,plain,(
% 1.29/0.56    $false),
% 1.29/0.56    inference(subsumption_resolution,[],[f444,f108])).
% 1.29/0.56  fof(f108,plain,(
% 1.29/0.56    l1_pre_topc(sK3)),
% 1.29/0.56    inference(resolution,[],[f105,f65])).
% 1.29/0.56  fof(f65,plain,(
% 1.29/0.56    m1_pre_topc(sK3,sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f50,plain,(
% 1.29/0.56    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.29/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f20,f49,f48,f47,f46,f45,f44,f43])).
% 1.29/0.56  fof(f43,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f44,plain,(
% 1.29/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f45,plain,(
% 1.29/0.56    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f46,plain,(
% 1.29/0.56    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f47,plain,(
% 1.29/0.56    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f48,plain,(
% 1.29/0.56    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f49,plain,(
% 1.29/0.56    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.29/0.56    introduced(choice_axiom,[])).
% 1.29/0.56  fof(f20,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f19])).
% 1.29/0.56  fof(f19,plain,(
% 1.29/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f18])).
% 1.29/0.56  fof(f18,negated_conjecture,(
% 1.29/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.29/0.56    inference(negated_conjecture,[],[f17])).
% 1.29/0.56  fof(f17,conjecture,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.29/0.56  fof(f105,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.29/0.56    inference(resolution,[],[f80,f58])).
% 1.29/0.56  fof(f58,plain,(
% 1.29/0.56    l1_pre_topc(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f80,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f25])).
% 1.29/0.56  fof(f25,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f8])).
% 1.29/0.56  fof(f8,axiom,(
% 1.29/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.29/0.56  fof(f444,plain,(
% 1.29/0.56    ~l1_pre_topc(sK3)),
% 1.29/0.56    inference(resolution,[],[f442,f76])).
% 1.29/0.56  fof(f76,plain,(
% 1.29/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f22])).
% 1.29/0.56  fof(f22,plain,(
% 1.29/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f7])).
% 1.29/0.56  fof(f7,axiom,(
% 1.29/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.29/0.56  fof(f442,plain,(
% 1.29/0.56    ~l1_struct_0(sK3)),
% 1.29/0.56    inference(subsumption_resolution,[],[f311,f441])).
% 1.29/0.56  fof(f441,plain,(
% 1.29/0.56    v1_xboole_0(k2_struct_0(sK2))),
% 1.29/0.56    inference(subsumption_resolution,[],[f440,f98])).
% 1.29/0.56  fof(f98,plain,(
% 1.29/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.29/0.56    inference(equality_resolution,[],[f91])).
% 1.29/0.56  fof(f91,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.29/0.56    inference(cnf_transformation,[],[f54])).
% 1.29/0.56  fof(f54,plain,(
% 1.29/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.56    inference(flattening,[],[f53])).
% 1.29/0.56  fof(f53,plain,(
% 1.29/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.56    inference(nnf_transformation,[],[f1])).
% 1.29/0.56  fof(f1,axiom,(
% 1.29/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.56  fof(f440,plain,(
% 1.29/0.56    v1_xboole_0(k2_struct_0(sK2)) | ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))),
% 1.29/0.56    inference(resolution,[],[f438,f94])).
% 1.29/0.56  fof(f94,plain,(
% 1.29/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f55])).
% 1.29/0.56  fof(f55,plain,(
% 1.29/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.29/0.56    inference(nnf_transformation,[],[f3])).
% 1.29/0.56  fof(f3,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.56  fof(f438,plain,(
% 1.29/0.56    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | v1_xboole_0(k2_struct_0(sK2))),
% 1.29/0.56    inference(subsumption_resolution,[],[f437,f123])).
% 1.29/0.56  fof(f123,plain,(
% 1.29/0.56    m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.29/0.56    inference(backward_demodulation,[],[f101,f118])).
% 1.29/0.56  fof(f118,plain,(
% 1.29/0.56    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.29/0.56    inference(resolution,[],[f104,f107])).
% 1.29/0.56  fof(f107,plain,(
% 1.29/0.56    l1_pre_topc(sK2)),
% 1.29/0.56    inference(resolution,[],[f105,f63])).
% 1.29/0.56  fof(f63,plain,(
% 1.29/0.56    m1_pre_topc(sK2,sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f104,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.29/0.56    inference(resolution,[],[f75,f76])).
% 1.29/0.56  fof(f75,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f21])).
% 1.29/0.56  fof(f21,plain,(
% 1.29/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f6])).
% 1.29/0.56  fof(f6,axiom,(
% 1.29/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.29/0.56  fof(f101,plain,(
% 1.29/0.56    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.29/0.56    inference(forward_demodulation,[],[f71,f72])).
% 1.29/0.56  fof(f72,plain,(
% 1.29/0.56    sK5 = sK6),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f71,plain,(
% 1.29/0.56    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f437,plain,(
% 1.29/0.56    ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.29/0.56    inference(resolution,[],[f436,f395])).
% 1.29/0.56  fof(f395,plain,(
% 1.29/0.56    ( ! [X0] : (m1_connsp_2(k2_struct_0(sK2),sK3,X0) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f394,f98])).
% 1.29/0.56  fof(f394,plain,(
% 1.29/0.56    ( ! [X0] : (m1_connsp_2(k2_struct_0(sK2),sK3,X0) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X0,k2_struct_0(sK2)) | ~r1_tarski(k2_struct_0(sK2),k2_struct_0(sK2))) )),
% 1.29/0.56    inference(resolution,[],[f393,f94])).
% 1.29/0.56  fof(f393,plain,(
% 1.29/0.56    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) | m1_connsp_2(k2_struct_0(sK2),sK3,X2) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X2,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f392,f307])).
% 1.29/0.56  fof(f307,plain,(
% 1.29/0.56    u1_struct_0(sK3) = k2_struct_0(sK2)),
% 1.29/0.56    inference(backward_demodulation,[],[f119,f306])).
% 1.29/0.56  fof(f306,plain,(
% 1.29/0.56    k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.29/0.56    inference(subsumption_resolution,[],[f234,f305])).
% 1.29/0.56  fof(f305,plain,(
% 1.29/0.56    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.29/0.56    inference(forward_demodulation,[],[f304,f119])).
% 1.29/0.56  fof(f304,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2))),
% 1.29/0.56    inference(forward_demodulation,[],[f303,f118])).
% 1.29/0.56  fof(f303,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.29/0.56    inference(subsumption_resolution,[],[f296,f107])).
% 1.29/0.56  fof(f296,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 1.29/0.56    inference(resolution,[],[f289,f81])).
% 1.29/0.56  fof(f81,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f26])).
% 1.29/0.56  fof(f26,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f14])).
% 1.29/0.56  fof(f14,axiom,(
% 1.29/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.29/0.56  fof(f289,plain,(
% 1.29/0.56    m1_pre_topc(sK3,sK2)),
% 1.29/0.56    inference(subsumption_resolution,[],[f288,f108])).
% 1.29/0.56  fof(f288,plain,(
% 1.29/0.56    m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK3)),
% 1.29/0.56    inference(resolution,[],[f287,f77])).
% 1.29/0.56  fof(f77,plain,(
% 1.29/0.56    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f23])).
% 1.29/0.56  fof(f23,plain,(
% 1.29/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f13])).
% 1.29/0.56  fof(f13,axiom,(
% 1.29/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.29/0.56  fof(f287,plain,(
% 1.29/0.56    ~m1_pre_topc(sK3,sK3) | m1_pre_topc(sK3,sK2)),
% 1.29/0.56    inference(forward_demodulation,[],[f286,f122])).
% 1.29/0.56  fof(f122,plain,(
% 1.29/0.56    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 1.29/0.56    inference(backward_demodulation,[],[f69,f118])).
% 1.29/0.56  fof(f69,plain,(
% 1.29/0.56    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f286,plain,(
% 1.29/0.56    ~m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(sK3,sK2)),
% 1.29/0.56    inference(subsumption_resolution,[],[f283,f107])).
% 1.29/0.56  fof(f283,plain,(
% 1.29/0.56    ~m1_pre_topc(sK3,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | m1_pre_topc(sK3,sK2)),
% 1.29/0.56    inference(superposition,[],[f249,f118])).
% 1.29/0.56  fof(f249,plain,(
% 1.29/0.56    ( ! [X3] : (~m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))) | ~l1_pre_topc(X3) | m1_pre_topc(sK3,X3)) )),
% 1.29/0.56    inference(resolution,[],[f79,f108])).
% 1.29/0.56  fof(f79,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | m1_pre_topc(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f51])).
% 1.29/0.56  fof(f51,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(nnf_transformation,[],[f24])).
% 1.29/0.56  fof(f24,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.29/0.56    inference(ennf_transformation,[],[f10])).
% 1.29/0.56  fof(f10,axiom,(
% 1.29/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.29/0.56  fof(f234,plain,(
% 1.29/0.56    ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.29/0.56    inference(resolution,[],[f232,f92])).
% 1.29/0.56  fof(f92,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.29/0.56    inference(cnf_transformation,[],[f54])).
% 1.29/0.56  fof(f232,plain,(
% 1.29/0.56    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))),
% 1.29/0.56    inference(forward_demodulation,[],[f231,f118])).
% 1.29/0.56  fof(f231,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK2),k2_struct_0(sK3))),
% 1.29/0.56    inference(forward_demodulation,[],[f230,f119])).
% 1.29/0.56  fof(f230,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.29/0.56    inference(subsumption_resolution,[],[f224,f108])).
% 1.29/0.56  fof(f224,plain,(
% 1.29/0.56    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) | ~l1_pre_topc(sK3)),
% 1.29/0.56    inference(resolution,[],[f217,f81])).
% 1.29/0.56  fof(f217,plain,(
% 1.29/0.56    m1_pre_topc(sK2,sK3)),
% 1.29/0.56    inference(forward_demodulation,[],[f216,f122])).
% 1.29/0.56  fof(f216,plain,(
% 1.29/0.56    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.29/0.56    inference(forward_demodulation,[],[f212,f118])).
% 1.29/0.56  fof(f212,plain,(
% 1.29/0.56    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.29/0.56    inference(resolution,[],[f193,f107])).
% 1.29/0.56  fof(f193,plain,(
% 1.29/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 1.29/0.56    inference(duplicate_literal_removal,[],[f192])).
% 1.29/0.56  fof(f192,plain,(
% 1.29/0.56    ( ! [X0] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.29/0.56    inference(resolution,[],[f78,f77])).
% 1.29/0.56  fof(f78,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f51])).
% 1.29/0.56  fof(f119,plain,(
% 1.29/0.56    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.29/0.56    inference(resolution,[],[f104,f108])).
% 1.29/0.56  fof(f392,plain,(
% 1.29/0.56    ( ! [X2] : (m1_connsp_2(k2_struct_0(sK2),sK3,X2) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X2,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f391,f64])).
% 1.29/0.56  fof(f64,plain,(
% 1.29/0.56    ~v2_struct_0(sK3)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f391,plain,(
% 1.29/0.56    ( ! [X2] : (m1_connsp_2(k2_struct_0(sK2),sK3,X2) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X2,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f390,f141])).
% 1.29/0.56  fof(f141,plain,(
% 1.29/0.56    v2_pre_topc(sK3)),
% 1.29/0.56    inference(resolution,[],[f138,f65])).
% 1.29/0.56  fof(f138,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f136,f58])).
% 1.29/0.56  fof(f136,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) )),
% 1.29/0.56    inference(resolution,[],[f87,f57])).
% 1.29/0.56  fof(f57,plain,(
% 1.29/0.56    v2_pre_topc(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f87,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f36])).
% 1.29/0.56  fof(f36,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.29/0.56    inference(flattening,[],[f35])).
% 1.29/0.56  fof(f35,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f5])).
% 1.29/0.56  fof(f5,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.29/0.56  fof(f390,plain,(
% 1.29/0.56    ( ! [X2] : (m1_connsp_2(k2_struct_0(sK2),sK3,X2) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X2,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f388,f108])).
% 1.29/0.56  fof(f388,plain,(
% 1.29/0.56    ( ! [X2] : (m1_connsp_2(k2_struct_0(sK2),sK3,X2) | ~m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(X2,k2_struct_0(sK2))) )),
% 1.29/0.56    inference(resolution,[],[f386,f360])).
% 1.29/0.56  fof(f360,plain,(
% 1.29/0.56    v3_pre_topc(k2_struct_0(sK2),sK3)),
% 1.29/0.56    inference(subsumption_resolution,[],[f359,f141])).
% 1.29/0.56  fof(f359,plain,(
% 1.29/0.56    v3_pre_topc(k2_struct_0(sK2),sK3) | ~v2_pre_topc(sK3)),
% 1.29/0.56    inference(subsumption_resolution,[],[f358,f108])).
% 1.29/0.56  fof(f358,plain,(
% 1.29/0.56    v3_pre_topc(k2_struct_0(sK2),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.29/0.56    inference(superposition,[],[f86,f306])).
% 1.29/0.56  fof(f86,plain,(
% 1.29/0.56    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f34])).
% 1.29/0.56  fof(f34,plain,(
% 1.29/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.29/0.56    inference(flattening,[],[f33])).
% 1.29/0.56  fof(f33,plain,(
% 1.29/0.56    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f11])).
% 1.29/0.56  fof(f11,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.29/0.56  fof(f386,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~v3_pre_topc(X0,X1) | m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f385,f164])).
% 1.29/0.56  fof(f164,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(X2,X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0)) )),
% 1.29/0.56    inference(resolution,[],[f95,f89])).
% 1.29/0.56  fof(f89,plain,(
% 1.29/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f40])).
% 1.29/0.56  fof(f40,plain,(
% 1.29/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/0.56    inference(flattening,[],[f39])).
% 1.29/0.56  fof(f39,plain,(
% 1.29/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/0.56    inference(ennf_transformation,[],[f2])).
% 1.29/0.56  fof(f2,axiom,(
% 1.29/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.29/0.56  fof(f95,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f42])).
% 1.29/0.56  fof(f42,plain,(
% 1.29/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.29/0.56    inference(flattening,[],[f41])).
% 1.29/0.56  fof(f41,plain,(
% 1.29/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.29/0.56    inference(ennf_transformation,[],[f4])).
% 1.29/0.56  fof(f4,axiom,(
% 1.29/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.29/0.56  fof(f385,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (m1_connsp_2(X0,X1,X2) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | v1_xboole_0(X0) | ~m1_subset_1(X2,X0)) )),
% 1.29/0.56    inference(resolution,[],[f83,f89])).
% 1.29/0.56  fof(f83,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f30])).
% 1.29/0.56  fof(f30,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f29])).
% 1.29/0.56  fof(f29,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f12])).
% 1.29/0.56  fof(f12,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.29/0.56  fof(f436,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f435,f309])).
% 1.29/0.56  fof(f309,plain,(
% 1.29/0.56    v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1))),
% 1.29/0.56    inference(backward_demodulation,[],[f125,f306])).
% 1.29/0.56  fof(f125,plain,(
% 1.29/0.56    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 1.29/0.56    inference(backward_demodulation,[],[f120,f119])).
% 1.29/0.56  fof(f120,plain,(
% 1.29/0.56    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 1.29/0.56    inference(backward_demodulation,[],[f67,f117])).
% 1.29/0.56  fof(f117,plain,(
% 1.29/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.29/0.56    inference(resolution,[],[f104,f61])).
% 1.29/0.56  fof(f61,plain,(
% 1.29/0.56    l1_pre_topc(sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f67,plain,(
% 1.29/0.56    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f435,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5)) )),
% 1.29/0.56    inference(forward_demodulation,[],[f434,f307])).
% 1.29/0.56  fof(f434,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5)) )),
% 1.29/0.56    inference(forward_demodulation,[],[f433,f117])).
% 1.29/0.56  fof(f433,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f432,f308])).
% 1.29/0.56  fof(f308,plain,(
% 1.29/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 1.29/0.56    inference(backward_demodulation,[],[f124,f306])).
% 1.29/0.56  fof(f124,plain,(
% 1.29/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 1.29/0.56    inference(backward_demodulation,[],[f121,f119])).
% 1.29/0.56  fof(f121,plain,(
% 1.29/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 1.29/0.56    inference(backward_demodulation,[],[f68,f117])).
% 1.29/0.56  fof(f68,plain,(
% 1.29/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f432,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f431,f307])).
% 1.29/0.56  fof(f431,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f430,f117])).
% 1.29/0.56  fof(f430,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f429,f93])).
% 1.29/0.56  fof(f93,plain,(
% 1.29/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f55])).
% 1.29/0.56  fof(f429,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f428,f307])).
% 1.29/0.56  fof(f428,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f427,f123])).
% 1.29/0.56  fof(f427,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f426,f307])).
% 1.29/0.56  fof(f426,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f425,f123])).
% 1.29/0.56  fof(f425,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f424,f118])).
% 1.29/0.56  fof(f424,plain,(
% 1.29/0.56    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(forward_demodulation,[],[f423,f118])).
% 1.29/0.56  fof(f423,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f422,f56])).
% 1.29/0.56  fof(f56,plain,(
% 1.29/0.56    ~v2_struct_0(sK0)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f422,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f421,f57])).
% 1.29/0.56  fof(f421,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f420,f58])).
% 1.29/0.56  fof(f420,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f419,f59])).
% 1.29/0.56  fof(f59,plain,(
% 1.29/0.56    ~v2_struct_0(sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f419,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f418,f60])).
% 1.29/0.56  fof(f60,plain,(
% 1.29/0.56    v2_pre_topc(sK1)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f418,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f417,f61])).
% 1.29/0.56  fof(f417,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f416,f62])).
% 1.29/0.56  fof(f62,plain,(
% 1.29/0.56    ~v2_struct_0(sK2)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f416,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f415,f64])).
% 1.29/0.56  fof(f415,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f414,f65])).
% 1.29/0.56  fof(f414,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f413,f74])).
% 1.29/0.56  fof(f74,plain,(
% 1.29/0.56    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f413,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f412,f217])).
% 1.29/0.56  fof(f412,plain,(
% 1.29/0.56    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.29/0.56    inference(resolution,[],[f411,f100])).
% 1.29/0.56  fof(f100,plain,(
% 1.29/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.29/0.56    inference(backward_demodulation,[],[f73,f72])).
% 1.29/0.56  fof(f73,plain,(
% 1.29/0.56    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f411,plain,(
% 1.29/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | ~m1_connsp_2(X5,X3,X4) | ~r1_tarski(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.29/0.56    inference(resolution,[],[f102,f66])).
% 1.29/0.56  fof(f66,plain,(
% 1.29/0.56    v1_funct_1(sK4)),
% 1.29/0.56    inference(cnf_transformation,[],[f50])).
% 1.29/0.56  fof(f102,plain,(
% 1.29/0.56    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(subsumption_resolution,[],[f96,f88])).
% 1.29/0.56  fof(f88,plain,(
% 1.29/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f38])).
% 1.29/0.56  fof(f38,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.29/0.56    inference(flattening,[],[f37])).
% 1.29/0.56  fof(f37,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f15])).
% 1.29/0.56  fof(f15,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.29/0.56  fof(f96,plain,(
% 1.29/0.56    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(equality_resolution,[],[f85])).
% 1.29/0.56  fof(f85,plain,(
% 1.29/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f52])).
% 1.29/0.56  fof(f52,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(nnf_transformation,[],[f32])).
% 1.29/0.56  fof(f32,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f31])).
% 1.29/0.56  fof(f31,plain,(
% 1.29/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f16])).
% 1.29/0.56  fof(f16,axiom,(
% 1.29/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).
% 1.29/0.56  fof(f311,plain,(
% 1.29/0.56    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK3)),
% 1.29/0.56    inference(backward_demodulation,[],[f134,f306])).
% 1.29/0.56  fof(f134,plain,(
% 1.29/0.56    ~v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 1.29/0.56    inference(subsumption_resolution,[],[f133,f64])).
% 1.29/0.56  fof(f133,plain,(
% 1.29/0.56    ~v1_xboole_0(k2_struct_0(sK3)) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 1.29/0.56    inference(superposition,[],[f82,f119])).
% 1.29/0.56  fof(f82,plain,(
% 1.29/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.29/0.56    inference(cnf_transformation,[],[f28])).
% 1.29/0.56  fof(f28,plain,(
% 1.29/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.29/0.56    inference(flattening,[],[f27])).
% 1.29/0.56  fof(f27,plain,(
% 1.29/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.29/0.56    inference(ennf_transformation,[],[f9])).
% 1.29/0.56  fof(f9,axiom,(
% 1.29/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.29/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.29/0.56  % SZS output end Proof for theBenchmark
% 1.29/0.56  % (27683)------------------------------
% 1.29/0.56  % (27683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (27683)Termination reason: Refutation
% 1.29/0.56  
% 1.29/0.56  % (27683)Memory used [KB]: 6652
% 1.29/0.56  % (27683)Time elapsed: 0.113 s
% 1.29/0.56  % (27683)------------------------------
% 1.29/0.56  % (27683)------------------------------
% 1.29/0.56  % (27679)Success in time 0.196 s
%------------------------------------------------------------------------------
