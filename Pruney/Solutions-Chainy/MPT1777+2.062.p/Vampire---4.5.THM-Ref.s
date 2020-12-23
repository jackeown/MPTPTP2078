%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:11 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  137 (1185 expanded)
%              Number of leaves         :   23 ( 610 expanded)
%              Depth                    :   25
%              Number of atoms          :  866 (17997 expanded)
%              Number of equality atoms :   50 (2388 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f634,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f49,f50,f51,f58,f185,f237,f190,f67,f87,f564])).

fof(f564,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k2_struct_0(sK3))
      | ~ m1_subset_1(X4,k2_struct_0(sK2))
      | ~ m1_subset_1(X4,k2_struct_0(sK3))
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4)
      | r1_tmap_1(sK3,sK1,sK4,X4)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f563,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f19,f45,f44,f43,f42,f41,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f563,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k2_struct_0(sK3))
      | ~ m1_subset_1(X4,k2_struct_0(sK2))
      | ~ m1_subset_1(X4,k2_struct_0(sK3))
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4)
      | r1_tmap_1(sK3,sK1,sK4,X4)
      | ~ m1_pre_topc(sK3,X5)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f562,f226])).

fof(f226,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f225,f184])).

fof(f184,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f62,f181])).

fof(f181,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f141,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f141,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f127,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f127,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f51,f56,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f56,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f225,plain,(
    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(forward_demodulation,[],[f217,f181])).

fof(f217,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(unit_resulting_resolution,[],[f127,f127,f142,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f142,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f127,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f562,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k2_struct_0(sK3))
      | ~ m1_subset_1(X4,k2_struct_0(sK2))
      | ~ m1_subset_1(X4,k2_struct_0(sK3))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4)
      | r1_tmap_1(sK3,sK1,sK4,X4)
      | ~ m1_pre_topc(sK3,X5)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f555,f376])).

fof(f376,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f375,f188])).

fof(f188,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f164,f70])).

fof(f164,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f159,f71])).

fof(f159,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f51,f58,f75])).

fof(f375,plain,(
    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f365,f181])).

fof(f365,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f127,f333,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f333,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f165,f155])).

fof(f155,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | m1_pre_topc(X3,sK2) ) ),
    inference(forward_demodulation,[],[f148,f62])).

fof(f148,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X3,sK2) ) ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f165,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f159,f72])).

fof(f555,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
      | ~ r2_hidden(X4,k2_struct_0(sK3))
      | ~ m1_subset_1(X4,k2_struct_0(sK2))
      | ~ m1_subset_1(X4,k2_struct_0(sK3))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4)
      | r1_tmap_1(sK3,sK1,sK4,X4)
      | ~ m1_pre_topc(sK3,X5)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(superposition,[],[f551,f181])).

fof(f551,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(X1))
      | ~ r2_hidden(X0,k2_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK3))
      | ~ m1_pre_topc(X1,sK3)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f550,f68])).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f550,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK3))
      | ~ r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f549,f176])).

fof(f176,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f172,f161])).

fof(f161,plain,(
    v2_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f50,f51,f58,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f172,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f159,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f549,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k2_struct_0(sK3),sK3)
      | ~ r2_hidden(X0,k2_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK3))
      | ~ r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f548,f68])).

fof(f548,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_struct_0(sK3))
      | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK3)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK3))
      | ~ r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(forward_demodulation,[],[f547,f68])).

fof(f547,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_subset_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK3)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(sK3))
      | ~ r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK3)
      | ~ r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0)
      | r1_tmap_1(sK3,sK1,sK4,X0)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f546,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f546,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ r2_hidden(X14,X12)
      | ~ v3_pre_topc(X12,sK3)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X14,k2_struct_0(sK3))
      | ~ r1_tarski(X12,u1_struct_0(X13))
      | ~ m1_pre_topc(X13,sK3)
      | ~ r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14)
      | r1_tmap_1(sK3,sK1,sK4,X14)
      | ~ m1_pre_topc(sK3,X15)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f545,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f545,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_tarski(X12,u1_struct_0(X13))
      | ~ r2_hidden(X14,X12)
      | ~ v3_pre_topc(X12,sK3)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X14,k2_struct_0(sK3))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ m1_pre_topc(X13,sK3)
      | ~ r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14)
      | r1_tmap_1(sK3,sK1,sK4,X14)
      | ~ m1_pre_topc(sK3,X15)
      | v2_struct_0(sK3)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f544,f191])).

fof(f191,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f137,f188])).

fof(f137,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f60,f132])).

fof(f132,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f102,f70])).

fof(f102,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f54,f71])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f544,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_tarski(X12,u1_struct_0(X13))
      | ~ r2_hidden(X14,X12)
      | ~ v3_pre_topc(X12,sK3)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X14,k2_struct_0(sK3))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ m1_pre_topc(X13,sK3)
      | ~ r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,X14)
      | ~ m1_pre_topc(sK3,X15)
      | v2_struct_0(sK3)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(subsumption_resolution,[],[f540,f192])).

fof(f192,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f138,f188])).

fof(f138,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f61,f132])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f540,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ r1_tarski(X12,u1_struct_0(X13))
      | ~ r2_hidden(X14,X12)
      | ~ v3_pre_topc(X12,sK3)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | ~ m1_subset_1(X14,k2_struct_0(sK3))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ m1_pre_topc(X13,sK3)
      | ~ r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,X14)
      | ~ m1_pre_topc(sK3,X15)
      | v2_struct_0(sK3)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X15)
      | ~ v2_pre_topc(X15)
      | v2_struct_0(X15) ) ),
    inference(superposition,[],[f354,f188])).

fof(f354,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | ~ r1_tarski(X6,u1_struct_0(X7))
      | ~ r2_hidden(X8,X6)
      | ~ v3_pre_topc(X6,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_pre_topc(X7,X5)
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8)
      | ~ v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1))
      | r1_tmap_1(X5,sK1,sK4,X8)
      | ~ m1_pre_topc(X5,X9)
      | v2_struct_0(X5)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f353,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f353,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | ~ r1_tarski(X6,u1_struct_0(X7))
      | ~ r2_hidden(X8,X6)
      | ~ v3_pre_topc(X6,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_pre_topc(X7,X5)
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8)
      | ~ v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1))
      | r1_tmap_1(X5,sK1,sK4,X8)
      | ~ m1_pre_topc(X5,X9)
      | v2_struct_0(X5)
      | v2_struct_0(X7)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f352,f53])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f352,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | ~ r1_tarski(X6,u1_struct_0(X7))
      | ~ r2_hidden(X8,X6)
      | ~ v3_pre_topc(X6,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_pre_topc(X7,X5)
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8)
      | ~ v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1))
      | r1_tmap_1(X5,sK1,sK4,X8)
      | ~ m1_pre_topc(X5,X9)
      | v2_struct_0(X5)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f342,f54])).

fof(f342,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | ~ r1_tarski(X6,u1_struct_0(X7))
      | ~ r2_hidden(X8,X6)
      | ~ v3_pre_topc(X6,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_pre_topc(X7,X5)
      | ~ r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8)
      | ~ v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1))
      | r1_tmap_1(X5,sK1,sK4,X8)
      | ~ m1_pre_topc(X5,X9)
      | v2_struct_0(X5)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(superposition,[],[f118,f132])).

fof(f118,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X7))))
      | ~ r1_tarski(X11,u1_struct_0(X6))
      | ~ r2_hidden(X10,X11)
      | ~ v3_pre_topc(X11,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_pre_topc(X6,X9)
      | ~ r1_tmap_1(X6,X7,k3_tmap_1(X8,X7,X9,X6,sK4),X10)
      | ~ v1_funct_2(sK4,u1_struct_0(X9),u1_struct_0(X7))
      | r1_tmap_1(X9,X7,sK4,X10)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X9)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f116,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( ~ r1_tmap_1(X6,X7,k3_tmap_1(X8,X7,X9,X6,sK4),X10)
      | ~ r1_tarski(X11,u1_struct_0(X6))
      | ~ r2_hidden(X10,X11)
      | ~ v3_pre_topc(X11,X9)
      | ~ m1_subset_1(X10,u1_struct_0(X6))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_pre_topc(X6,X9)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X7))))
      | ~ v1_funct_2(sK4,u1_struct_0(X9),u1_struct_0(X7))
      | r1_tmap_1(X9,X7,sK4,X10)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X6,X8)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(resolution,[],[f59,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
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
      | r1_tmap_1(X3,X1,X4,X7)
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f66,f65])).

fof(f65,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f190,plain,(
    m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f63,f188])).

fof(f63,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f237,plain,(
    r2_hidden(sK5,k2_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f190,f198,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f198,plain,(
    ~ v1_xboole_0(k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f187,f188])).

fof(f187,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f57,f164,f78])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f185,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f88,f181])).

fof(f88,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f64,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f58,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:08 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (5315)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (5306)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5308)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (5314)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (5316)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (5305)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.55  % (5303)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.55  % (5313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (5321)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.56  % (5301)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (5304)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (5311)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.56  % (5318)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.56  % (5319)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.57  % (5310)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.61/0.57  % (5312)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.61/0.57  % (5302)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.57  % (5316)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % (5309)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.61/0.58  % (5320)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.61/0.58  % (5317)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f634,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f49,f50,f51,f58,f185,f237,f190,f67,f87,f564])).
% 1.61/0.58  fof(f564,plain,(
% 1.61/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_struct_0(sK3)) | ~m1_subset_1(X4,k2_struct_0(sK2)) | ~m1_subset_1(X4,k2_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4) | r1_tmap_1(sK3,sK1,sK4,X4) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f563,f55])).
% 1.61/0.58  fof(f55,plain,(
% 1.61/0.58    ~v2_struct_0(sK2)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f46,plain,(
% 1.61/0.58    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f19,f45,f44,f43,f42,f41,f40,f39])).
% 1.61/0.58  fof(f39,plain,(
% 1.61/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f41,plain,(
% 1.61/0.58    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f42,plain,(
% 1.61/0.58    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f44,plain,(
% 1.61/0.58    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f45,plain,(
% 1.61/0.58    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f19,plain,(
% 1.61/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.61/0.58    inference(flattening,[],[f18])).
% 1.61/0.58  fof(f18,plain,(
% 1.61/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f17])).
% 1.61/0.58  fof(f17,negated_conjecture,(
% 1.61/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.61/0.58    inference(negated_conjecture,[],[f16])).
% 1.61/0.58  fof(f16,conjecture,(
% 1.61/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.61/0.58  fof(f563,plain,(
% 1.61/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_struct_0(sK3)) | ~m1_subset_1(X4,k2_struct_0(sK2)) | ~m1_subset_1(X4,k2_struct_0(sK3)) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4) | r1_tmap_1(sK3,sK1,sK4,X4) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f562,f226])).
% 1.61/0.58  fof(f226,plain,(
% 1.61/0.58    m1_pre_topc(sK2,sK3)),
% 1.61/0.58    inference(forward_demodulation,[],[f225,f184])).
% 1.61/0.58  fof(f184,plain,(
% 1.61/0.58    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 1.61/0.58    inference(backward_demodulation,[],[f62,f181])).
% 1.61/0.58  fof(f181,plain,(
% 1.61/0.58    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f141,f70])).
% 1.61/0.58  fof(f70,plain,(
% 1.61/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f20])).
% 1.61/0.58  fof(f20,plain,(
% 1.61/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.61/0.58  fof(f141,plain,(
% 1.61/0.58    l1_struct_0(sK2)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f127,f71])).
% 1.61/0.58  fof(f71,plain,(
% 1.61/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f6])).
% 1.61/0.58  fof(f6,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.61/0.58  fof(f127,plain,(
% 1.61/0.58    l1_pre_topc(sK2)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f51,f56,f75])).
% 1.61/0.58  fof(f75,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f24])).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.61/0.58  fof(f56,plain,(
% 1.61/0.58    m1_pre_topc(sK2,sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f62,plain,(
% 1.61/0.58    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f225,plain,(
% 1.61/0.58    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.61/0.58    inference(forward_demodulation,[],[f217,f181])).
% 1.61/0.58  fof(f217,plain,(
% 1.61/0.58    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f127,f127,f142,f73])).
% 1.61/0.58  fof(f73,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f47])).
% 1.61/0.58  fof(f47,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(nnf_transformation,[],[f23])).
% 1.61/0.58  fof(f23,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f10])).
% 1.61/0.58  fof(f10,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.61/0.58  fof(f142,plain,(
% 1.61/0.58    m1_pre_topc(sK2,sK2)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f127,f72])).
% 1.61/0.58  fof(f72,plain,(
% 1.61/0.58    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f22])).
% 1.61/0.58  fof(f22,plain,(
% 1.61/0.58    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.61/0.58  fof(f562,plain,(
% 1.61/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k2_struct_0(sK3)) | ~m1_subset_1(X4,k2_struct_0(sK2)) | ~m1_subset_1(X4,k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4) | r1_tmap_1(sK3,sK1,sK4,X4) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f555,f376])).
% 1.61/0.58  fof(f376,plain,(
% 1.61/0.58    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.61/0.58    inference(forward_demodulation,[],[f375,f188])).
% 1.61/0.58  fof(f188,plain,(
% 1.61/0.58    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f164,f70])).
% 1.61/0.58  fof(f164,plain,(
% 1.61/0.58    l1_struct_0(sK3)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f159,f71])).
% 1.61/0.58  fof(f159,plain,(
% 1.61/0.58    l1_pre_topc(sK3)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f51,f58,f75])).
% 1.61/0.58  fof(f375,plain,(
% 1.61/0.58    r1_tarski(u1_struct_0(sK3),k2_struct_0(sK2))),
% 1.61/0.58    inference(forward_demodulation,[],[f365,f181])).
% 1.61/0.58  fof(f365,plain,(
% 1.61/0.58    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f127,f333,f76])).
% 1.61/0.58  fof(f76,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f25])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).
% 1.61/0.58  fof(f333,plain,(
% 1.61/0.58    m1_pre_topc(sK3,sK2)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f165,f155])).
% 1.61/0.58  fof(f155,plain,(
% 1.61/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK3) | m1_pre_topc(X3,sK2)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f148,f62])).
% 1.61/0.58  fof(f148,plain,(
% 1.61/0.58    ( ! [X3] : (~m1_pre_topc(X3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X3,sK2)) )),
% 1.61/0.58    inference(resolution,[],[f127,f77])).
% 1.61/0.58  fof(f77,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f9])).
% 1.61/0.58  fof(f9,axiom,(
% 1.61/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.61/0.58  fof(f165,plain,(
% 1.61/0.58    m1_pre_topc(sK3,sK3)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f159,f72])).
% 1.61/0.58  fof(f555,plain,(
% 1.61/0.58    ( ! [X4,X5] : (~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | ~r2_hidden(X4,k2_struct_0(sK3)) | ~m1_subset_1(X4,k2_struct_0(sK2)) | ~m1_subset_1(X4,k2_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X5,sK1,sK3,sK2,sK4),X4) | r1_tmap_1(sK3,sK1,sK4,X4) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.61/0.58    inference(superposition,[],[f551,f181])).
% 1.61/0.58  fof(f551,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_struct_0(sK3),u1_struct_0(X1)) | ~r2_hidden(X0,k2_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f550,f68])).
% 1.61/0.58  fof(f68,plain,(
% 1.61/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.61/0.58  fof(f550,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(sK3)) | ~r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f549,f176])).
% 1.61/0.58  fof(f176,plain,(
% 1.61/0.58    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.61/0.58    inference(subsumption_resolution,[],[f172,f161])).
% 1.61/0.58  fof(f161,plain,(
% 1.61/0.58    v2_pre_topc(sK3)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f50,f51,f58,f82])).
% 1.61/0.58  fof(f82,plain,(
% 1.61/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f34])).
% 1.61/0.58  fof(f34,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.61/0.58    inference(flattening,[],[f33])).
% 1.61/0.58  fof(f33,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.61/0.58  fof(f172,plain,(
% 1.61/0.58    v3_pre_topc(k2_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.61/0.58    inference(resolution,[],[f159,f81])).
% 1.61/0.58  fof(f81,plain,(
% 1.61/0.58    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0) | ~v2_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f32])).
% 1.61/0.58  fof(f32,plain,(
% 1.61/0.58    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.61/0.58    inference(flattening,[],[f31])).
% 1.61/0.58  fof(f31,plain,(
% 1.61/0.58    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f11])).
% 1.61/0.58  fof(f11,axiom,(
% 1.61/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.61/0.58  fof(f549,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~v3_pre_topc(k2_struct_0(sK3),sK3) | ~r2_hidden(X0,k2_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(sK3)) | ~r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f548,f68])).
% 1.61/0.58  fof(f548,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_struct_0(sK3)) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK3)),sK3) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(sK3)) | ~r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f547,f68])).
% 1.61/0.58  fof(f547,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_subset_1(k2_struct_0(sK3))) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK3)),sK3) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(sK3)) | ~r1_tarski(k2_subset_1(k2_struct_0(sK3)),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK1,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.61/0.58    inference(resolution,[],[f546,f69])).
% 1.61/0.58  fof(f69,plain,(
% 1.61/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.61/0.58  fof(f546,plain,(
% 1.61/0.58    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3))) | ~r2_hidden(X14,X12) | ~v3_pre_topc(X12,sK3) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~m1_subset_1(X14,k2_struct_0(sK3)) | ~r1_tarski(X12,u1_struct_0(X13)) | ~m1_pre_topc(X13,sK3) | ~r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14) | r1_tmap_1(sK3,sK1,sK4,X14) | ~m1_pre_topc(sK3,X15) | v2_struct_0(X13) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f545,f57])).
% 1.61/0.58  fof(f57,plain,(
% 1.61/0.58    ~v2_struct_0(sK3)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f545,plain,(
% 1.61/0.58    ( ! [X14,X12,X15,X13] : (~r1_tarski(X12,u1_struct_0(X13)) | ~r2_hidden(X14,X12) | ~v3_pre_topc(X12,sK3) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~m1_subset_1(X14,k2_struct_0(sK3)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X13,sK3) | ~r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14) | r1_tmap_1(sK3,sK1,sK4,X14) | ~m1_pre_topc(sK3,X15) | v2_struct_0(sK3) | v2_struct_0(X13) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f544,f191])).
% 1.61/0.58  fof(f191,plain,(
% 1.61/0.58    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 1.61/0.58    inference(backward_demodulation,[],[f137,f188])).
% 1.61/0.58  fof(f137,plain,(
% 1.61/0.58    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 1.61/0.58    inference(backward_demodulation,[],[f60,f132])).
% 1.61/0.58  fof(f132,plain,(
% 1.61/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f102,f70])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    l1_struct_0(sK1)),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f54,f71])).
% 1.61/0.58  fof(f54,plain,(
% 1.61/0.58    l1_pre_topc(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f60,plain,(
% 1.61/0.58    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f544,plain,(
% 1.61/0.58    ( ! [X14,X12,X15,X13] : (~r1_tarski(X12,u1_struct_0(X13)) | ~r2_hidden(X14,X12) | ~v3_pre_topc(X12,sK3) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~m1_subset_1(X14,k2_struct_0(sK3)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X13,sK3) | ~r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,X14) | ~m1_pre_topc(sK3,X15) | v2_struct_0(sK3) | v2_struct_0(X13) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f540,f192])).
% 1.61/0.58  fof(f192,plain,(
% 1.61/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 1.61/0.58    inference(backward_demodulation,[],[f138,f188])).
% 1.61/0.58  fof(f138,plain,(
% 1.61/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 1.61/0.58    inference(backward_demodulation,[],[f61,f132])).
% 1.61/0.58  fof(f61,plain,(
% 1.61/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f540,plain,(
% 1.61/0.58    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~r1_tarski(X12,u1_struct_0(X13)) | ~r2_hidden(X14,X12) | ~v3_pre_topc(X12,sK3) | ~m1_subset_1(X14,u1_struct_0(X13)) | ~m1_subset_1(X14,k2_struct_0(sK3)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X13,sK3) | ~r1_tmap_1(X13,sK1,k3_tmap_1(X15,sK1,sK3,X13,sK4),X14) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,X14) | ~m1_pre_topc(sK3,X15) | v2_struct_0(sK3) | v2_struct_0(X13) | ~l1_pre_topc(X15) | ~v2_pre_topc(X15) | v2_struct_0(X15)) )),
% 1.61/0.58    inference(superposition,[],[f354,f188])).
% 1.61/0.58  fof(f354,plain,(
% 1.61/0.58    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | ~r1_tarski(X6,u1_struct_0(X7)) | ~r2_hidden(X8,X6) | ~v3_pre_topc(X6,X5) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(X7,X5) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8) | ~v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1)) | r1_tmap_1(X5,sK1,sK4,X8) | ~m1_pre_topc(X5,X9) | v2_struct_0(X5) | v2_struct_0(X7) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f353,f52])).
% 1.61/0.58  fof(f52,plain,(
% 1.61/0.58    ~v2_struct_0(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f353,plain,(
% 1.61/0.58    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | ~r1_tarski(X6,u1_struct_0(X7)) | ~r2_hidden(X8,X6) | ~v3_pre_topc(X6,X5) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(X7,X5) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8) | ~v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1)) | r1_tmap_1(X5,sK1,sK4,X8) | ~m1_pre_topc(X5,X9) | v2_struct_0(X5) | v2_struct_0(X7) | v2_struct_0(sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f352,f53])).
% 1.61/0.58  fof(f53,plain,(
% 1.61/0.58    v2_pre_topc(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f352,plain,(
% 1.61/0.58    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | ~r1_tarski(X6,u1_struct_0(X7)) | ~r2_hidden(X8,X6) | ~v3_pre_topc(X6,X5) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(X7,X5) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8) | ~v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1)) | r1_tmap_1(X5,sK1,sK4,X8) | ~m1_pre_topc(X5,X9) | v2_struct_0(X5) | v2_struct_0(X7) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f342,f54])).
% 1.61/0.58  fof(f342,plain,(
% 1.61/0.58    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | ~r1_tarski(X6,u1_struct_0(X7)) | ~r2_hidden(X8,X6) | ~v3_pre_topc(X6,X5) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(X7,X5) | ~r1_tmap_1(X7,sK1,k3_tmap_1(X9,sK1,X5,X7,sK4),X8) | ~v1_funct_2(sK4,u1_struct_0(X5),k2_struct_0(sK1)) | r1_tmap_1(X5,sK1,sK4,X8) | ~m1_pre_topc(X5,X9) | v2_struct_0(X5) | v2_struct_0(X7) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.61/0.58    inference(superposition,[],[f118,f132])).
% 1.61/0.58  fof(f118,plain,(
% 1.61/0.58    ( ! [X6,X10,X8,X7,X11,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X7)))) | ~r1_tarski(X11,u1_struct_0(X6)) | ~r2_hidden(X10,X11) | ~v3_pre_topc(X11,X9) | ~m1_subset_1(X10,u1_struct_0(X6)) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))) | ~m1_pre_topc(X6,X9) | ~r1_tmap_1(X6,X7,k3_tmap_1(X8,X7,X9,X6,sK4),X10) | ~v1_funct_2(sK4,u1_struct_0(X9),u1_struct_0(X7)) | r1_tmap_1(X9,X7,sK4,X10) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f116,f83])).
% 1.61/0.58  fof(f83,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f36,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.61/0.58    inference(flattening,[],[f35])).
% 1.61/0.58  fof(f35,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f14])).
% 1.61/0.58  fof(f14,axiom,(
% 1.61/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.61/0.58  fof(f116,plain,(
% 1.61/0.58    ( ! [X6,X10,X8,X7,X11,X9] : (~r1_tmap_1(X6,X7,k3_tmap_1(X8,X7,X9,X6,sK4),X10) | ~r1_tarski(X11,u1_struct_0(X6)) | ~r2_hidden(X10,X11) | ~v3_pre_topc(X11,X9) | ~m1_subset_1(X10,u1_struct_0(X6)) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))) | ~m1_pre_topc(X6,X9) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X7)))) | ~v1_funct_2(sK4,u1_struct_0(X9),u1_struct_0(X7)) | r1_tmap_1(X9,X7,sK4,X10) | ~m1_pre_topc(X9,X8) | v2_struct_0(X9) | ~m1_pre_topc(X6,X8) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.61/0.58    inference(resolution,[],[f59,f85])).
% 1.61/0.58  fof(f85,plain,(
% 1.61/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X7) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f80])).
% 1.61/0.58  fof(f80,plain,(
% 1.61/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f48])).
% 1.61/0.58  fof(f48,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.61/0.58    inference(nnf_transformation,[],[f30])).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.61/0.58    inference(flattening,[],[f29])).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f15])).
% 1.61/0.58  fof(f15,axiom,(
% 1.61/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 1.61/0.58  fof(f59,plain,(
% 1.61/0.58    v1_funct_1(sK4)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f87,plain,(
% 1.61/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.61/0.58    inference(backward_demodulation,[],[f66,f65])).
% 1.61/0.58  fof(f65,plain,(
% 1.61/0.58    sK5 = sK6),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f66,plain,(
% 1.61/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f67,plain,(
% 1.61/0.58    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f190,plain,(
% 1.61/0.58    m1_subset_1(sK5,k2_struct_0(sK3))),
% 1.61/0.58    inference(backward_demodulation,[],[f63,f188])).
% 1.61/0.58  fof(f63,plain,(
% 1.61/0.58    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f237,plain,(
% 1.61/0.58    r2_hidden(sK5,k2_struct_0(sK3))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f190,f198,f84])).
% 1.61/0.58  fof(f84,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f38])).
% 1.61/0.58  fof(f38,plain,(
% 1.61/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.61/0.58    inference(flattening,[],[f37])).
% 1.61/0.58  fof(f37,plain,(
% 1.61/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.61/0.58    inference(ennf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.61/0.58  fof(f198,plain,(
% 1.61/0.58    ~v1_xboole_0(k2_struct_0(sK3))),
% 1.61/0.58    inference(forward_demodulation,[],[f187,f188])).
% 1.61/0.58  fof(f187,plain,(
% 1.61/0.58    ~v1_xboole_0(u1_struct_0(sK3))),
% 1.61/0.58    inference(unit_resulting_resolution,[],[f57,f164,f78])).
% 1.61/0.58  fof(f78,plain,(
% 1.61/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.61/0.58    inference(flattening,[],[f27])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f8])).
% 1.61/0.58  fof(f8,axiom,(
% 1.61/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.61/0.58  fof(f185,plain,(
% 1.61/0.58    m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.61/0.58    inference(backward_demodulation,[],[f88,f181])).
% 1.61/0.58  fof(f88,plain,(
% 1.61/0.58    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.61/0.58    inference(forward_demodulation,[],[f64,f65])).
% 1.61/0.58  fof(f64,plain,(
% 1.61/0.58    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f58,plain,(
% 1.61/0.58    m1_pre_topc(sK3,sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f51,plain,(
% 1.61/0.58    l1_pre_topc(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f50,plain,(
% 1.61/0.58    v2_pre_topc(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  fof(f49,plain,(
% 1.61/0.58    ~v2_struct_0(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f46])).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (5316)------------------------------
% 1.61/0.58  % (5316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (5316)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (5316)Memory used [KB]: 6908
% 1.61/0.58  % (5316)Time elapsed: 0.137 s
% 1.61/0.58  % (5316)------------------------------
% 1.61/0.58  % (5316)------------------------------
% 1.61/0.58  % (5300)Success in time 0.216 s
%------------------------------------------------------------------------------
