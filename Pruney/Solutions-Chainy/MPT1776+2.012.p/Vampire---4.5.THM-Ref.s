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
% DateTime   : Thu Dec  3 13:18:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 884 expanded)
%              Number of leaves         :   24 ( 423 expanded)
%              Depth                    :   32
%              Number of atoms          : 1315 (18438 expanded)
%              Number of equality atoms :   42 (1054 expanded)
%              Maximal formula depth    :   32 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f100,f117,f160,f167,f174,f200])).

fof(f200,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f198,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
      | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
    & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
      | r1_tmap_1(sK5,sK2,sK6,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_pre_topc(sK4,sK5)
    & m1_pre_topc(sK4,sK3)
    & v1_tsep_1(sK4,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
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
                              ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK2,X4,X5) )
                              & ( r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK2,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK2,X4,X5) )
                            & ( r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK2,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,X1)
                    & v1_tsep_1(X2,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK2,X4,X5) )
                          & ( r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK2,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK3)
                  & v1_tsep_1(X2,sK3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK2,X4,X5) )
                        & ( r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK2,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK3)
                & v1_tsep_1(X2,sK3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                        | ~ r1_tmap_1(X3,sK2,X4,X5) )
                      & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                        | r1_tmap_1(X3,sK2,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK4,X3)
              & m1_pre_topc(sK4,sK3)
              & v1_tsep_1(sK4,sK3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                      | ~ r1_tmap_1(X3,sK2,X4,X5) )
                    & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6)
                      | r1_tmap_1(X3,sK2,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK4,X3)
            & m1_pre_topc(sK4,sK3)
            & v1_tsep_1(sK4,sK3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                    | ~ r1_tmap_1(sK5,sK2,X4,X5) )
                  & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                    | r1_tmap_1(sK5,sK2,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_pre_topc(sK4,sK5)
          & m1_pre_topc(sK4,sK3)
          & v1_tsep_1(sK4,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                  | ~ r1_tmap_1(sK5,sK2,X4,X5) )
                & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6)
                  | r1_tmap_1(sK5,sK2,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_pre_topc(sK4,sK5)
        & m1_pre_topc(sK4,sK3)
        & v1_tsep_1(sK4,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
                | ~ r1_tmap_1(sK5,sK2,sK6,X5) )
              & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
                | r1_tmap_1(sK5,sK2,sK6,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_pre_topc(sK4,sK5)
      & m1_pre_topc(sK4,sK3)
      & v1_tsep_1(sK4,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
              | ~ r1_tmap_1(sK5,sK2,sK6,X5) )
            & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
              | r1_tmap_1(sK5,sK2,sK6,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
            | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
          & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
            | r1_tmap_1(sK5,sK2,sK6,sK7) )
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

% (5560)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f38,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
          | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
        & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6)
          | r1_tmap_1(sK5,sK2,sK6,sK7) )
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
        | ~ r1_tmap_1(sK5,sK2,sK6,sK7) )
      & ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
        | r1_tmap_1(sK5,sK2,sK6,sK7) )
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
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
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
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
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f198,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f197,f51])).

fof(f51,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f196,f52])).

fof(f52,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f195,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f195,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f194,f48])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f194,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f193,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f192,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f192,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f191,f56])).

fof(f56,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f191,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f190,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f190,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f189,f54])).

fof(f54,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f189,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f188,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f188,plain,
    ( ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f187,f58])).

fof(f58,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f187,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f186,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f63,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f185,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f184,f101])).

fof(f101,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f64,f65])).

fof(f65,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f184,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f183,f62])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f183,plain,
    ( ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f182,f93])).

fof(f93,plain,
    ( r1_tmap_1(sK5,sK2,sK6,sK7)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl9_1
  <=> r1_tmap_1(sK5,sK2,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f182,plain,
    ( ~ r1_tmap_1(sK5,sK2,sK6,sK7)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
    | ~ v1_funct_1(sK6)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl9_2 ),
    inference(resolution,[],[f175,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f175,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7)
    | spl9_2 ),
    inference(forward_demodulation,[],[f98,f65])).

fof(f98,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_2
  <=> r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f174,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl9_6 ),
    inference(subsumption_resolution,[],[f172,f60])).

fof(f60,plain,(
    v1_tsep_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f172,plain,
    ( ~ v1_tsep_1(sK4,sK3)
    | spl9_6 ),
    inference(subsumption_resolution,[],[f171,f54])).

fof(f171,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | ~ v1_tsep_1(sK4,sK3)
    | spl9_6 ),
    inference(resolution,[],[f170,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f170,plain,
    ( ~ sP0(sK3,sK4)
    | spl9_6 ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f169,plain,
    ( ~ sP0(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | spl9_6 ),
    inference(subsumption_resolution,[],[f168,f51])).

fof(f168,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ sP0(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | spl9_6 ),
    inference(resolution,[],[f159,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(u1_struct_0(X2),X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f124,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ sP0(X3,X2)
      | v3_pre_topc(u1_struct_0(X2),X3) ) ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X0,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f122,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f28,f27])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f159,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_6
  <=> v3_pre_topc(u1_struct_0(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f167,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl9_4
    | spl9_5 ),
    inference(subsumption_resolution,[],[f165,f115])).

fof(f115,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl9_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f165,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_5 ),
    inference(resolution,[],[f164,f68])).

% (5541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f164,plain,
    ( ~ l1_struct_0(sK4)
    | spl9_5 ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f163,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | spl9_5 ),
    inference(resolution,[],[f162,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | spl9_5 ),
    inference(subsumption_resolution,[],[f161,f101])).

fof(f161,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | spl9_5 ),
    inference(resolution,[],[f155,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f155,plain,
    ( ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_5
  <=> r2_hidden(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f160,plain,
    ( ~ spl9_5
    | ~ spl9_6
    | spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f151,f96,f92,f157,f153])).

fof(f151,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f150,f54])).

fof(f150,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f149,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f149,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f148,f52])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7,u1_struct_0(X0))
        | ~ v3_pre_topc(u1_struct_0(X0),sK3)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f147,f70])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK4)) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f145,f48])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f144,f49])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f143,f50])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f142,f51])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f138,f55])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f135,f58])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f133,f62])).

% (5568)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f131,f101])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f128,f94])).

fof(f94,plain,
    ( ~ r1_tmap_1(sK5,sK2,sK6,sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK5,sK2,sK6,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK4))
        | ~ r2_hidden(sK7,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f85,f102])).

fof(f102,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f97,f65])).

fof(f97,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f85,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | r1_tmap_1(X3,X0,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X1)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X2,X3)
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( ( r1_tmap_1(X3,X0,X4,X6)
                                      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) ) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  | X6 != X7
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X1)
                                  | ~ m1_subset_1(X7,u1_struct_0(X2)) )
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      | ~ m1_pre_topc(X2,X3)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f117,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f106,f113])).

fof(f106,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f103,f52])).

fof(f103,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f100,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f66,f96,f92])).

fof(f66,plain,
    ( r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | r1_tmap_1(sK5,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f67,f96,f92])).

fof(f67,plain,
    ( ~ r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)
    | ~ r1_tmap_1(sK5,sK2,sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

% (5552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (5549)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (5550)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (5555)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (5545)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (5546)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (5540)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (5543)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (5564)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (5544)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (5545)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (5561)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (5551)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (5567)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (5554)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f99,f100,f117,f160,f167,f174,f200])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    ~spl9_1 | spl9_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    $false | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~v2_struct_0(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    (((((((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f31,f38,f37,f36,f35,f34,f33,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(X1,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK3) & v1_tsep_1(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(X2,sK2,k3_tmap_1(sK3,sK2,X3,X2,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK3) & v1_tsep_1(X2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | ~r1_tmap_1(X3,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,X3,sK4,X4),X6) | r1_tmap_1(X3,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK4,X3) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | ~r1_tmap_1(sK5,sK2,X4,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,X4),X6) | r1_tmap_1(sK5,sK2,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & m1_pre_topc(sK4,sK5) & m1_pre_topc(sK4,sK3) & v1_tsep_1(sK4,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) & v1_funct_1(sK6))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X5] : (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,X5)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (5560)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X6] : ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),X6) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => ((~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)) & (r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v2_pre_topc(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_pre_topc(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f195,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f194,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v2_pre_topc(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    l1_pre_topc(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~v2_struct_0(sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f191,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m1_pre_topc(sK5,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ~v2_struct_0(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f189,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_pre_topc(sK4,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_funct_1(sK6)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f187,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f186,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2))))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f185,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.21/0.51    inference(forward_demodulation,[],[f64,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    sK7 = sK8),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    m1_subset_1(sK8,u1_struct_0(sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f183,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    m1_pre_topc(sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl9_1 | spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f182,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    r1_tmap_1(sK5,sK2,sK6,sK7) | ~spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl9_1 <=> r1_tmap_1(sK5,sK2,sK6,sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~r1_tmap_1(sK5,sK2,sK6,sK7) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl9_2),
% 0.21/0.51    inference(resolution,[],[f175,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7) | spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f98,f65])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl9_2 <=> r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl9_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    $false | spl9_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f172,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v1_tsep_1(sK4,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ~v1_tsep_1(sK4,sK3) | spl9_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f171,f54])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3) | spl9_6),
% 0.21/0.51    inference(resolution,[],[f170,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~sP0(sK3,sK4) | spl9_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f52])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~sP0(sK3,sK4) | ~l1_pre_topc(sK3) | spl9_6),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f51])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~v2_pre_topc(sK3) | ~sP0(sK3,sK4) | ~l1_pre_topc(sK3) | spl9_6),
% 0.21/0.51    inference(resolution,[],[f159,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X2,X3] : (v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | ~l1_pre_topc(X3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f124,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP0(X0,X1) | m1_pre_topc(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~sP0(X3,X2) | v3_pre_topc(u1_struct_0(X2),X3)) )),
% 0.21/0.51    inference(resolution,[],[f122,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X0,X2) | v3_pre_topc(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(definition_folding,[],[f24,f28,f27])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~v3_pre_topc(u1_struct_0(sK4),sK3) | spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl9_6 <=> v3_pre_topc(u1_struct_0(sK4),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~spl9_4 | spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    $false | (~spl9_4 | spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    l1_pre_topc(sK4) | ~spl9_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl9_4 <=> l1_pre_topc(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | spl9_5),
% 0.21/0.51    inference(resolution,[],[f164,f68])).
% 0.21/0.51  % (5541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ~l1_struct_0(sK4) | spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f53])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~l1_struct_0(sK4) | v2_struct_0(sK4) | spl9_5),
% 0.21/0.51    inference(resolution,[],[f162,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK4)) | spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f101])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | spl9_5),
% 0.21/0.51    inference(resolution,[],[f155,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ~r2_hidden(sK7,u1_struct_0(sK4)) | spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl9_5 <=> r2_hidden(sK7,u1_struct_0(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ~spl9_5 | ~spl9_6 | spl9_1 | ~spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f151,f96,f92,f157,f153])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~v3_pre_topc(u1_struct_0(sK4),sK3) | ~r2_hidden(sK7,u1_struct_0(sK4)) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f54])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ~v3_pre_topc(u1_struct_0(sK4),sK3) | ~r2_hidden(sK7,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK3) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(resolution,[],[f149,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~r2_hidden(sK7,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f148,f52])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK7,u1_struct_0(X0)) | ~v3_pre_topc(u1_struct_0(X0),sK3) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(resolution,[],[f147,f70])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK4))) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f47])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f48])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f49])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f50])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f51])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f141,f52])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f53])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f54])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f55])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f56])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f57])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f58])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f59])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f62])).
% 0.21/0.51  % (5568)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f132,f63])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f101])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~r1_tmap_1(sK5,sK2,sK6,sK7) | spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f92])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tmap_1(sK5,sK2,sK6,sK7) | ~r1_tarski(X0,u1_struct_0(sK4)) | ~r2_hidden(sK7,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK2)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK2)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_2),
% 0.21/0.51    inference(resolution,[],[f85,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK7) | ~spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f97,f65])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X1))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f106,f113])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    l1_pre_topc(sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f52])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    l1_pre_topc(sK4) | ~l1_pre_topc(sK3)),
% 0.21/0.51    inference(resolution,[],[f69,f54])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl9_1 | spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f96,f92])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | r1_tmap_1(sK5,sK2,sK6,sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f96,f92])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ~r1_tmap_1(sK4,sK2,k3_tmap_1(sK3,sK2,sK5,sK4,sK6),sK8) | ~r1_tmap_1(sK5,sK2,sK6,sK7)),
% 0.21/0.51    inference(cnf_transformation,[],[f39])).
% 0.21/0.51  % (5552)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (5549)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (5550)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (5555)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (5545)------------------------------
% 0.21/0.52  % (5545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5545)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (5545)Memory used [KB]: 6396
% 0.21/0.52  % (5545)Time elapsed: 0.101 s
% 0.21/0.52  % (5545)------------------------------
% 0.21/0.52  % (5545)------------------------------
% 0.21/0.52  % (5536)Success in time 0.164 s
%------------------------------------------------------------------------------
