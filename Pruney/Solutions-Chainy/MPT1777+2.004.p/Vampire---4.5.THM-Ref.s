%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 794 expanded)
%              Number of leaves         :   31 ( 404 expanded)
%              Depth                    :   25
%              Number of atoms          :  919 (12073 expanded)
%              Number of equality atoms :   74 (1596 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f160,f179,f209,f253,f556,f558])).

fof(f558,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | spl9_13 ),
    inference(subsumption_resolution,[],[f252,f294])).

fof(f294,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f293,f119])).

fof(f119,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f116,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f22,f53,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f52,plain,
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

fof(f53,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f116,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f67,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f67,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f293,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f170,f81])).

fof(f81,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f164,f119])).

fof(f164,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f84,f73])).

fof(f73,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f252,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl9_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f556,plain,
    ( ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_12 ),
    inference(subsumption_resolution,[],[f554,f248])).

fof(f248,plain,
    ( ~ sP7(sK3,sK2,sK5)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl9_12
  <=> sP7(sK3,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f554,plain,
    ( sP7(sK3,sK2,sK5)
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f550,f151])).

fof(f151,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl9_3
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f550,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | sP7(sK3,sK2,X0) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f548,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f548,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | sP7(sK3,X0,X1)
        | ~ r2_hidden(X1,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f546,f347])).

fof(f347,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f204,f338])).

fof(f338,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(trivial_inequality_removal,[],[f337])).

fof(f337,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f178,f227])).

fof(f227,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f226,f127])).

fof(f127,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f124,f62])).

fof(f124,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f86])).

fof(f69,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f226,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f215,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f215,plain,
    ( v1_pre_topc(sK3)
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f210,f73])).

fof(f210,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl9_5 ),
    inference(resolution,[],[f174,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f174,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl9_5
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f178,plain,
    ( ! [X4,X5] :
        ( sK3 != g1_pre_topc(X4,X5)
        | u1_struct_0(sK2) = X4 )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl9_6
  <=> ! [X5,X4] :
        ( sK3 != g1_pre_topc(X4,X5)
        | u1_struct_0(sK2) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f204,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f203,f126])).

fof(f126,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f125,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f123,f62])).

fof(f123,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f69,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f203,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f202,f127])).

fof(f202,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(superposition,[],[f90,f131])).

fof(f131,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f129,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f129,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f127,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f546,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | sP7(sK3,X0,X1)
        | ~ r2_hidden(X1,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f542,f107])).

fof(f542,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ v3_pre_topc(X1,sK3)
        | ~ r1_tarski(X1,u1_struct_0(X2))
        | sP7(sK3,X2,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f358,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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

fof(f358,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ r1_tarski(X2,u1_struct_0(X4))
        | sP7(sK3,X4,X3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f108,f338])).

fof(f108,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | sP7(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f108_D])).

fof(f108_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r2_hidden(X7,X5)
          | ~ v3_pre_topc(X5,X3)
          | ~ r1_tarski(X5,u1_struct_0(X2)) )
    <=> ~ sP7(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f253,plain,
    ( ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f244,f250,f246])).

fof(f244,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f243,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f243,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f242,f61])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f241,f62])).

fof(f241,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f240,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f240,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f239,f64])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f239,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f238,f65])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f238,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f237,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f237,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f236,f67])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f235,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f235,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f234,f69])).

fof(f234,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f233,f70])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f233,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f232,f71])).

fof(f71,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f232,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f231,f72])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f231,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f230,f74])).

fof(f74,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

% (6237)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f230,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f229,f142])).

fof(f142,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f76,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f229,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f228,f78])).

fof(f78,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f228,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(resolution,[],[f205,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
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
      | v2_struct_0(X0)
      | ~ sP7(X3,X2,X7) ) ),
    inference(general_splitting,[],[f104,f108_D])).

fof(f104,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f205,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(forward_demodulation,[],[f77,f76])).

fof(f77,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f209,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f206,f119])).

fof(f206,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_5 ),
    inference(resolution,[],[f175,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f175,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f179,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f167,f177,f173])).

fof(f167,plain,(
    ! [X4,X5] :
      ( sK3 != g1_pre_topc(X4,X5)
      | u1_struct_0(sK2) = X4
      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f96,f73])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f160,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f158,f66])).

fof(f158,plain,
    ( v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f157,f128])).

fof(f128,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f119,f80])).

fof(f157,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f155,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f155,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_4
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f156,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f147,f153,f149])).

fof(f147,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f142,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:34:17 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (6223)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (6230)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (6231)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (6241)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (6238)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (6233)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (6220)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (6229)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (6235)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (6225)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (6219)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (6223)Refutation not found, incomplete strategy% (6223)------------------------------
% 0.22/0.52  % (6223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6223)Memory used [KB]: 6524
% 0.22/0.52  % (6223)Time elapsed: 0.092 s
% 0.22/0.52  % (6223)------------------------------
% 0.22/0.52  % (6223)------------------------------
% 0.22/0.52  % (6227)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (6218)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (6243)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (6225)Refutation not found, incomplete strategy% (6225)------------------------------
% 0.22/0.53  % (6225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6225)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6225)Memory used [KB]: 1918
% 0.22/0.53  % (6225)Time elapsed: 0.072 s
% 0.22/0.53  % (6225)------------------------------
% 0.22/0.53  % (6225)------------------------------
% 0.22/0.53  % (6226)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (6221)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (6222)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (6236)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (6224)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (6240)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (6234)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (6228)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (6219)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f559,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f156,f160,f179,f209,f253,f556,f558])).
% 0.22/0.54  fof(f558,plain,(
% 0.22/0.54    spl9_13),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f557])).
% 0.22/0.54  fof(f557,plain,(
% 0.22/0.54    $false | spl9_13),
% 0.22/0.54    inference(subsumption_resolution,[],[f252,f294])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f293,f119])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    l1_pre_topc(sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f116,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f22,f53,f52,f51,f50,f49,f48,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f19])).
% 0.22/0.54  fof(f19,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f67,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.54    inference(resolution,[],[f170,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f164,f119])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(superposition,[],[f84,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | spl9_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f250])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    spl9_13 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.54  fof(f556,plain,(
% 0.22/0.54    ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f555])).
% 0.22/0.54  fof(f555,plain,(
% 0.22/0.54    $false | (~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_12)),
% 0.22/0.54    inference(subsumption_resolution,[],[f554,f248])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    ~sP7(sK3,sK2,sK5) | spl9_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f246])).
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    spl9_12 <=> sP7(sK3,sK2,sK5)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.54  fof(f554,plain,(
% 0.22/0.54    sP7(sK3,sK2,sK5) | (~spl9_3 | ~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(resolution,[],[f550,f151])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl9_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f149])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    spl9_3 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.54  fof(f550,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | sP7(sK3,sK2,X0)) ) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(resolution,[],[f548,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f98])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f548,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | sP7(sK3,X0,X1) | ~r2_hidden(X1,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f546,f347])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(backward_demodulation,[],[f204,f338])).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f337])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(superposition,[],[f178,f227])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~spl9_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f226,f127])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    l1_pre_topc(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f124,f62])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f69,f86])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    m1_pre_topc(sK3,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~spl9_5),
% 0.22/0.54    inference(resolution,[],[f215,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.54  fof(f215,plain,(
% 0.22/0.54    v1_pre_topc(sK3) | ~spl9_5),
% 0.22/0.54    inference(forward_demodulation,[],[f210,f73])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl9_5),
% 0.22/0.54    inference(resolution,[],[f174,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl9_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    spl9_5 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X4,X5] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4) ) | ~spl9_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl9_6 <=> ! [X5,X4] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f203,f126])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v2_pre_topc(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f125,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f62])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.54    inference(resolution,[],[f69,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f202,f127])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 0.22/0.54    inference(superposition,[],[f90,f131])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f129,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    l1_struct_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f127,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.54  fof(f546,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(sK2),sK3) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | sP7(sK3,X0,X1) | ~r2_hidden(X1,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(resolution,[],[f542,f107])).
% 0.22/0.54  fof(f542,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,u1_struct_0(sK2)) | ~v3_pre_topc(X1,sK3) | ~r1_tarski(X1,u1_struct_0(X2)) | sP7(sK3,X2,X0) | ~r2_hidden(X0,X1)) ) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(resolution,[],[f358,f102])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f358,plain,(
% 0.22/0.54    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | ~r1_tarski(X2,u1_struct_0(X4)) | sP7(sK3,X4,X3)) ) | (~spl9_5 | ~spl9_6)),
% 0.22/0.54    inference(superposition,[],[f108,f338])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ( ! [X2,X7,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~r1_tarski(X5,u1_struct_0(X2)) | sP7(X3,X2,X7)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f108_D])).
% 0.22/0.54  fof(f108_D,plain,(
% 0.22/0.54    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~r1_tarski(X5,u1_struct_0(X2))) ) <=> ~sP7(X3,X2,X7)) )),
% 0.22/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    ~spl9_12 | ~spl9_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f244,f250,f246])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f243,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f242,f61])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f241,f62])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f240,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ~v2_struct_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f239,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    v2_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f238,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    l1_pre_topc(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f237,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ~v2_struct_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f236,f67])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f235,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~v2_struct_0(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f234,f69])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f233,f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    v1_funct_1(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f232,f71])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f231,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f230,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  % (6237)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f229,f142])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.54    inference(forward_demodulation,[],[f75,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    sK5 = sK6),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f228,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 0.22/0.54    inference(resolution,[],[f205,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP7(X3,X2,X7)) )),
% 0.22/0.54    inference(general_splitting,[],[f104,f108_D])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.54    inference(forward_demodulation,[],[f77,f76])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.54    inference(cnf_transformation,[],[f54])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    spl9_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    $false | spl9_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f206,f119])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ~l1_pre_topc(sK2) | spl9_5),
% 0.22/0.54    inference(resolution,[],[f175,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | spl9_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f173])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    ~spl9_5 | spl9_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f167,f177,f173])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X4,X5] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 0.22/0.54    inference(superposition,[],[f96,f73])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ~spl9_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    $false | ~spl9_4),
% 0.22/0.54    inference(subsumption_resolution,[],[f158,f66])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    v2_struct_0(sK2) | ~spl9_4),
% 0.22/0.54    inference(subsumption_resolution,[],[f157,f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    l1_struct_0(sK2)),
% 0.22/0.54    inference(resolution,[],[f119,f80])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl9_4),
% 0.22/0.54    inference(resolution,[],[f155,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~spl9_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f153])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    spl9_4 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    spl9_3 | spl9_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f147,f153,f149])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.54    inference(resolution,[],[f142,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (6219)------------------------------
% 0.22/0.54  % (6219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6219)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (6219)Memory used [KB]: 11001
% 0.22/0.54  % (6219)Time elapsed: 0.111 s
% 0.22/0.54  % (6219)------------------------------
% 0.22/0.54  % (6219)------------------------------
% 0.22/0.55  % (6217)Success in time 0.183 s
%------------------------------------------------------------------------------
