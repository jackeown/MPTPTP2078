%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:30 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  202 (3610 expanded)
%              Number of leaves         :   28 (1590 expanded)
%              Depth                    :   31
%              Number of atoms          : 1323 (59559 expanded)
%              Number of equality atoms :   35 (4077 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f653,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f124,f330,f367,f633,f652])).

fof(f652,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f650,f634])).

fof(f634,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl12_2 ),
    inference(forward_demodulation,[],[f122,f77])).

fof(f77,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f46,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
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
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK0,X2,X4) )
                        & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                          | r1_tmap_1(X1,sK0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                      & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                        | r1_tmap_1(sK1,sK0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_pre_topc(X3,sK1)
              & v1_tsep_1(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | ~ r1_tmap_1(sK1,sK0,X2,X4) )
                    & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5)
                      | r1_tmap_1(sK1,sK0,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_pre_topc(X3,sK1)
            & v1_tsep_1(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                  & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                    | r1_tmap_1(sK1,sK0,sK2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_pre_topc(X3,sK1)
          & v1_tsep_1(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
                & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5)
                  | r1_tmap_1(sK1,sK0,sK2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_pre_topc(X3,sK1)
        & v1_tsep_1(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
              & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
                | r1_tmap_1(sK1,sK0,sK2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_pre_topc(sK3,sK1)
      & v1_tsep_1(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | ~ r1_tmap_1(sK1,sK0,sK2,X4) )
            & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
              | r1_tmap_1(sK1,sK0,sK2,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
          & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
            | r1_tmap_1(sK1,sK0,sK2,sK4) )
          & sK4 = X5
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
        & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5)
          | r1_tmap_1(sK1,sK0,sK2,sK4) )
        & sK4 = X5
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
      & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
      & sK4 = sK5
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f122,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f650,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f649,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f649,plain,
    ( v2_struct_0(sK3)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f638,f74])).

fof(f74,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f638,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl12_1 ),
    inference(resolution,[],[f636,f125])).

fof(f125,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f76,f77])).

fof(f76,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f635,f75])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,u1_struct_0(X0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4) )
    | ~ spl12_1 ),
    inference(resolution,[],[f117,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) ) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f67])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f68])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f69])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f70])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f71,f104])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl12_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f633,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_15 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | spl12_1
    | ~ spl12_2
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f630,f206])).

fof(f206,plain,
    ( ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f205,f63])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f204,f64])).

fof(f204,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f203,f65])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f202,f66])).

fof(f202,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f201,f67])).

fof(f201,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f200,f68])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f199,f69])).

fof(f199,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f198,f70])).

fof(f198,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f197,f71])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f196,f72])).

fof(f196,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f195,f74])).

fof(f195,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f194,f75])).

fof(f194,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f193,f125])).

fof(f193,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f192,f118])).

fof(f118,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f192,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP10(sK3,sK1,sK4)
    | ~ spl12_2 ),
    inference(resolution,[],[f126,f111])).

fof(f111,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP10(X3,X1,X6) ) ),
    inference(general_splitting,[],[f105,f110_D])).

fof(f110,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP10(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f110_D])).

fof(f110_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP10(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
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
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f126,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f121,f77])).

fof(f121,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f630,plain,
    ( sP10(sK3,sK1,sK4)
    | ~ spl12_15 ),
    inference(resolution,[],[f629,f368])).

fof(f368,plain,(
    r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f332,f365])).

fof(f365,plain,(
    r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f364,f273])).

fof(f273,plain,(
    r1_tarski(sK8(sK3,sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f211,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f211,plain,(
    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f210,f72])).

fof(f210,plain,
    ( m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f209,f131])).

fof(f131,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f130,f67])).

fof(f130,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f127,f68])).

fof(f127,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f74,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f209,plain,
    ( m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f208,f133])).

fof(f133,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f129,f68])).

fof(f129,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f74,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f208,plain,
    ( m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f207,f125])).

fof(f207,plain,
    ( m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f144,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f144,plain,(
    m1_connsp_2(sK8(sK3,sK4),sK3,sK4) ),
    inference(subsumption_resolution,[],[f143,f72])).

fof(f143,plain,
    ( m1_connsp_2(sK8(sK3,sK4),sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f142,f131])).

fof(f142,plain,
    ( m1_connsp_2(sK8(sK3,sK4),sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f140,f133])).

fof(f140,plain,
    ( m1_connsp_2(sK8(sK3,sK4),sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f125,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK8(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK8(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f364,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK8(sK3,sK4),X0)
      | r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f363,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f363,plain,(
    r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f362,f125])).

fof(f362,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK8(sK3,sK4)) ),
    inference(resolution,[],[f317,f144])).

fof(f317,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK8(sK3,sK4),sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r2_hidden(X3,sK8(sK3,sK4)) ) ),
    inference(subsumption_resolution,[],[f316,f72])).

fof(f316,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK8(sK3,sK4),sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r2_hidden(X3,sK8(sK3,sK4))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f315,f131])).

fof(f315,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK8(sK3,sK4),sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r2_hidden(X3,sK8(sK3,sK4))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f270,f133])).

fof(f270,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK8(sK3,sK4),sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3))
      | r2_hidden(X3,sK8(sK3,sK4))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f211,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f332,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f172,f75])).

fof(f172,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ r2_hidden(X2,u1_struct_0(sK3))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f171,f66])).

fof(f171,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f170,f67])).

fof(f170,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f150,f160])).

fof(f160,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f159,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f158,f68])).

fof(f158,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f157,f73])).

fof(f73,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f157,plain,
    ( ~ v1_tsep_1(sK3,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f146,f74])).

fof(f146,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f132,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f132,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f128,f68])).

fof(f128,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f74,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f150,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,u1_struct_0(sK3))
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f132,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(sK7(X0,X1,X4),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK6(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK7(X0,X1,X4),X1)
                    & m1_connsp_2(sK7(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK6(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK7(X0,X1,X4),X1)
        & m1_connsp_2(sK7(X0,X1,X4),X0,X4)
        & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f629,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0))
        | sP10(X0,sK1,sK4) )
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f628,f75])).

fof(f628,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | sP10(X0,sK1,sK4) )
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f627,f365])).

fof(f627,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | sP10(X0,sK1,sK4) )
    | ~ spl12_15 ),
    inference(resolution,[],[f340,f325])).

fof(f325,plain,
    ( m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl12_15
  <=> m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f340,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X10),sK1,X12)
      | ~ r2_hidden(X10,u1_struct_0(sK3))
      | ~ r1_tarski(sK7(sK1,u1_struct_0(sK3),X10),u1_struct_0(X11))
      | ~ m1_subset_1(X10,u1_struct_0(sK1))
      | sP10(X11,sK1,X12) ) ),
    inference(resolution,[],[f164,f110])).

fof(f164,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f163,f66])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f162,f67])).

fof(f162,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f161,f68])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f160])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f132,f82])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f367,plain,(
    spl12_16 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl12_16 ),
    inference(subsumption_resolution,[],[f365,f329])).

fof(f329,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | spl12_16 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl12_16
  <=> r2_hidden(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f330,plain,
    ( spl12_15
    | ~ spl12_16 ),
    inference(avatar_split_clause,[],[f321,f327,f323])).

fof(f321,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) ),
    inference(resolution,[],[f168,f75])).

fof(f168,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X1,u1_struct_0(sK3))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) ) ),
    inference(subsumption_resolution,[],[f167,f66])).

fof(f167,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f166,f67])).

fof(f166,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f165,f68])).

fof(f165,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f149,f160])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
      | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f132,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | m1_connsp_2(sK7(X0,X1,X4),X0,X4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f124,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f78,f120,f116])).

fof(f78,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f79,f120,f116])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (10847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (10870)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (10849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (10858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (10862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (10855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (10860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (10852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (10869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (10851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (10850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (10854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (10853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (10871)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10876)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (10865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (10874)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (10869)Refutation not found, incomplete strategy% (10869)------------------------------
% 1.45/0.55  % (10869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (10867)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (10869)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (10869)Memory used [KB]: 11001
% 1.45/0.55  % (10869)Time elapsed: 0.068 s
% 1.45/0.55  % (10869)------------------------------
% 1.45/0.55  % (10869)------------------------------
% 1.45/0.55  % (10863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (10857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (10877)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.55  % (10868)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (10866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.56  % (10859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  % (10873)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.56  % (10856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.56  % (10864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (10855)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f653,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(avatar_sat_refutation,[],[f123,f124,f330,f367,f633,f652])).
% 1.45/0.56  fof(f652,plain,(
% 1.45/0.56    ~spl12_1 | spl12_2),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f651])).
% 1.45/0.56  fof(f651,plain,(
% 1.45/0.56    $false | (~spl12_1 | spl12_2)),
% 1.45/0.56    inference(subsumption_resolution,[],[f650,f634])).
% 1.45/0.56  fof(f634,plain,(
% 1.45/0.56    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl12_2),
% 1.45/0.56    inference(forward_demodulation,[],[f122,f77])).
% 1.45/0.56  fof(f77,plain,(
% 1.45/0.56    sK4 = sK5),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f46,f45,f44,f43,f42,f41])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f42,plain,(
% 1.45/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f39])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.56    inference(nnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/0.56    inference(flattening,[],[f16])).
% 1.45/0.56  fof(f16,plain,(
% 1.45/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,negated_conjecture,(
% 1.45/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.45/0.56    inference(negated_conjecture,[],[f14])).
% 1.45/0.56  fof(f14,conjecture,(
% 1.45/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 1.45/0.56  fof(f122,plain,(
% 1.45/0.56    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl12_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f120])).
% 1.45/0.56  fof(f120,plain,(
% 1.45/0.56    spl12_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.45/0.56  fof(f650,plain,(
% 1.45/0.56    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl12_1),
% 1.45/0.56    inference(subsumption_resolution,[],[f649,f72])).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ~v2_struct_0(sK3)),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  fof(f649,plain,(
% 1.45/0.56    v2_struct_0(sK3) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl12_1),
% 1.45/0.56    inference(subsumption_resolution,[],[f638,f74])).
% 1.45/0.56  fof(f74,plain,(
% 1.45/0.56    m1_pre_topc(sK3,sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f47])).
% 1.45/0.56  fof(f638,plain,(
% 1.45/0.56    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl12_1),
% 1.45/0.56    inference(resolution,[],[f636,f125])).
% 1.45/0.56  fof(f125,plain,(
% 1.45/0.56    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.45/0.56    inference(forward_demodulation,[],[f76,f77])).
% 1.45/0.57  fof(f76,plain,(
% 1.45/0.57    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f636,plain,(
% 1.45/0.57    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | ~spl12_1),
% 1.45/0.57    inference(subsumption_resolution,[],[f635,f75])).
% 1.45/0.57  fof(f75,plain,(
% 1.45/0.57    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f635,plain,(
% 1.45/0.57    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK4)) ) | ~spl12_1),
% 1.45/0.57    inference(resolution,[],[f117,f186])).
% 1.45/0.57  fof(f186,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f185,f63])).
% 1.45/0.57  fof(f63,plain,(
% 1.45/0.57    ~v2_struct_0(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f185,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f184,f64])).
% 1.45/0.57  fof(f64,plain,(
% 1.45/0.57    v2_pre_topc(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f184,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f183,f65])).
% 1.45/0.57  fof(f65,plain,(
% 1.45/0.57    l1_pre_topc(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f183,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f182,f66])).
% 1.45/0.57  fof(f66,plain,(
% 1.45/0.57    ~v2_struct_0(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f182,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f181,f67])).
% 1.45/0.57  fof(f67,plain,(
% 1.45/0.57    v2_pre_topc(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f181,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f180,f68])).
% 1.45/0.57  fof(f68,plain,(
% 1.45/0.57    l1_pre_topc(sK1)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f180,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f179,f69])).
% 1.45/0.57  fof(f69,plain,(
% 1.45/0.57    v1_funct_1(sK2)),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f179,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f176,f70])).
% 1.45/0.57  fof(f70,plain,(
% 1.45/0.57    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f176,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.45/0.57    inference(resolution,[],[f71,f104])).
% 1.45/0.57  fof(f104,plain,(
% 1.45/0.57    ( ! [X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f89])).
% 1.45/0.57  fof(f89,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f25])).
% 1.45/0.57  fof(f25,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f24])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f12])).
% 1.45/0.57  fof(f12,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 1.45/0.57  fof(f71,plain,(
% 1.45/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.45/0.57    inference(cnf_transformation,[],[f47])).
% 1.45/0.57  fof(f117,plain,(
% 1.45/0.57    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl12_1),
% 1.45/0.57    inference(avatar_component_clause,[],[f116])).
% 1.45/0.57  fof(f116,plain,(
% 1.45/0.57    spl12_1 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.45/0.57  fof(f633,plain,(
% 1.45/0.57    spl12_1 | ~spl12_2 | ~spl12_15),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f632])).
% 1.45/0.57  fof(f632,plain,(
% 1.45/0.57    $false | (spl12_1 | ~spl12_2 | ~spl12_15)),
% 1.45/0.57    inference(subsumption_resolution,[],[f630,f206])).
% 1.45/0.57  fof(f206,plain,(
% 1.45/0.57    ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f205,f63])).
% 1.45/0.57  fof(f205,plain,(
% 1.45/0.57    v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f204,f64])).
% 1.45/0.57  fof(f204,plain,(
% 1.45/0.57    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f203,f65])).
% 1.45/0.57  fof(f203,plain,(
% 1.45/0.57    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f202,f66])).
% 1.45/0.57  fof(f202,plain,(
% 1.45/0.57    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f201,f67])).
% 1.45/0.57  fof(f201,plain,(
% 1.45/0.57    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f200,f68])).
% 1.45/0.57  fof(f200,plain,(
% 1.45/0.57    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f199,f69])).
% 1.45/0.57  fof(f199,plain,(
% 1.45/0.57    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f198,f70])).
% 1.45/0.57  fof(f198,plain,(
% 1.45/0.57    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f197,f71])).
% 1.45/0.57  fof(f197,plain,(
% 1.45/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f196,f72])).
% 1.45/0.57  fof(f196,plain,(
% 1.45/0.57    v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f195,f74])).
% 1.45/0.57  fof(f195,plain,(
% 1.45/0.57    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f194,f75])).
% 1.45/0.57  fof(f194,plain,(
% 1.45/0.57    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f193,f125])).
% 1.45/0.57  fof(f193,plain,(
% 1.45/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | (spl12_1 | ~spl12_2)),
% 1.45/0.57    inference(subsumption_resolution,[],[f192,f118])).
% 1.45/0.57  fof(f118,plain,(
% 1.45/0.57    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl12_1),
% 1.45/0.57    inference(avatar_component_clause,[],[f116])).
% 1.45/0.57  fof(f192,plain,(
% 1.45/0.57    r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(sK3,sK1,sK4) | ~spl12_2),
% 1.45/0.57    inference(resolution,[],[f126,f111])).
% 1.45/0.57  fof(f111,plain,(
% 1.45/0.57    ( ! [X6,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP10(X3,X1,X6)) )),
% 1.45/0.57    inference(general_splitting,[],[f105,f110_D])).
% 1.45/0.57  fof(f110,plain,(
% 1.45/0.57    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP10(X3,X1,X6)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f110_D])).
% 1.45/0.57  fof(f110_D,plain,(
% 1.45/0.57    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP10(X3,X1,X6)) )),
% 1.45/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 1.45/0.57  fof(f105,plain,(
% 1.45/0.57    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(equality_resolution,[],[f91])).
% 1.45/0.57  fof(f91,plain,(
% 1.45/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f53])).
% 1.45/0.57  fof(f53,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(nnf_transformation,[],[f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f26])).
% 1.45/0.57  fof(f26,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f13])).
% 1.45/0.57  fof(f13,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 1.45/0.57  fof(f126,plain,(
% 1.45/0.57    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl12_2),
% 1.45/0.57    inference(forward_demodulation,[],[f121,f77])).
% 1.45/0.57  fof(f121,plain,(
% 1.45/0.57    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl12_2),
% 1.45/0.57    inference(avatar_component_clause,[],[f120])).
% 1.45/0.57  fof(f630,plain,(
% 1.45/0.57    sP10(sK3,sK1,sK4) | ~spl12_15),
% 1.45/0.57    inference(resolution,[],[f629,f368])).
% 1.45/0.57  fof(f368,plain,(
% 1.45/0.57    r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3))),
% 1.45/0.57    inference(subsumption_resolution,[],[f332,f365])).
% 1.45/0.57  fof(f365,plain,(
% 1.45/0.57    r2_hidden(sK4,u1_struct_0(sK3))),
% 1.45/0.57    inference(resolution,[],[f364,f273])).
% 1.45/0.57  fof(f273,plain,(
% 1.45/0.57    r1_tarski(sK8(sK3,sK4),u1_struct_0(sK3))),
% 1.45/0.57    inference(resolution,[],[f211,f102])).
% 1.45/0.57  fof(f102,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f62])).
% 1.45/0.57  fof(f62,plain,(
% 1.45/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.45/0.57    inference(nnf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.45/0.57  fof(f211,plain,(
% 1.45/0.57    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.45/0.57    inference(subsumption_resolution,[],[f210,f72])).
% 1.45/0.57  fof(f210,plain,(
% 1.45/0.57    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f209,f131])).
% 1.45/0.57  fof(f131,plain,(
% 1.45/0.57    v2_pre_topc(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f130,f67])).
% 1.45/0.57  fof(f130,plain,(
% 1.45/0.57    v2_pre_topc(sK3) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(subsumption_resolution,[],[f127,f68])).
% 1.45/0.57  fof(f127,plain,(
% 1.45/0.57    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.45/0.57    inference(resolution,[],[f74,f93])).
% 1.45/0.57  fof(f93,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f31])).
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.45/0.57    inference(flattening,[],[f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.45/0.57  fof(f209,plain,(
% 1.45/0.57    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f208,f133])).
% 1.45/0.57  fof(f133,plain,(
% 1.45/0.57    l1_pre_topc(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f129,f68])).
% 1.45/0.57  fof(f129,plain,(
% 1.45/0.57    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 1.45/0.57    inference(resolution,[],[f74,f80])).
% 1.45/0.57  fof(f80,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.45/0.57  fof(f208,plain,(
% 1.45/0.57    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.45/0.57    inference(subsumption_resolution,[],[f207,f125])).
% 1.45/0.57  fof(f207,plain,(
% 1.45/0.57    m1_subset_1(sK8(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.45/0.57    inference(resolution,[],[f144,f97])).
% 1.45/0.57  fof(f97,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f35])).
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/0.57    inference(flattening,[],[f34])).
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.45/0.57  fof(f144,plain,(
% 1.45/0.57    m1_connsp_2(sK8(sK3,sK4),sK3,sK4)),
% 1.45/0.57    inference(subsumption_resolution,[],[f143,f72])).
% 1.45/0.57  fof(f143,plain,(
% 1.45/0.57    m1_connsp_2(sK8(sK3,sK4),sK3,sK4) | v2_struct_0(sK3)),
% 1.58/0.57    inference(subsumption_resolution,[],[f142,f131])).
% 1.58/0.57  fof(f142,plain,(
% 1.58/0.57    m1_connsp_2(sK8(sK3,sK4),sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.58/0.57    inference(subsumption_resolution,[],[f140,f133])).
% 1.58/0.57  fof(f140,plain,(
% 1.58/0.57    m1_connsp_2(sK8(sK3,sK4),sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.58/0.57    inference(resolution,[],[f125,f98])).
% 1.58/0.57  fof(f98,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK8(X0,X1),X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f57])).
% 1.58/0.57  fof(f57,plain,(
% 1.58/0.57    ! [X0,X1] : (m1_connsp_2(sK8(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f56])).
% 1.58/0.57  fof(f56,plain,(
% 1.58/0.57    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK8(X0,X1),X0,X1))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(flattening,[],[f36])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 1.58/0.57  fof(f364,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(sK8(sK3,sK4),X0) | r2_hidden(sK4,X0)) )),
% 1.58/0.57    inference(resolution,[],[f363,f99])).
% 1.58/0.57  fof(f99,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f61])).
% 1.58/0.57  fof(f61,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f59,f60])).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f59,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(rectify,[],[f58])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.57    inference(nnf_transformation,[],[f38])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.57  fof(f363,plain,(
% 1.58/0.57    r2_hidden(sK4,sK8(sK3,sK4))),
% 1.58/0.57    inference(subsumption_resolution,[],[f362,f125])).
% 1.58/0.57  fof(f362,plain,(
% 1.58/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(sK4,sK8(sK3,sK4))),
% 1.58/0.57    inference(resolution,[],[f317,f144])).
% 1.58/0.57  fof(f317,plain,(
% 1.58/0.57    ( ! [X3] : (~m1_connsp_2(sK8(sK3,sK4),sK3,X3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r2_hidden(X3,sK8(sK3,sK4))) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f316,f72])).
% 1.58/0.57  fof(f316,plain,(
% 1.58/0.57    ( ! [X3] : (~m1_connsp_2(sK8(sK3,sK4),sK3,X3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r2_hidden(X3,sK8(sK3,sK4)) | v2_struct_0(sK3)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f315,f131])).
% 1.58/0.57  fof(f315,plain,(
% 1.58/0.57    ( ! [X3] : (~m1_connsp_2(sK8(sK3,sK4),sK3,X3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r2_hidden(X3,sK8(sK3,sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f270,f133])).
% 1.58/0.57  fof(f270,plain,(
% 1.58/0.57    ( ! [X3] : (~m1_connsp_2(sK8(sK3,sK4),sK3,X3) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r2_hidden(X3,sK8(sK3,sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.58/0.57    inference(resolution,[],[f211,f88])).
% 1.58/0.57  fof(f88,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(flattening,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.58/0.57  fof(f332,plain,(
% 1.58/0.57    ~r2_hidden(sK4,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(sK3))),
% 1.58/0.57    inference(resolution,[],[f172,f75])).
% 1.58/0.57  fof(f172,plain,(
% 1.58/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK1)) | ~r2_hidden(X2,u1_struct_0(sK3)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3))) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f171,f66])).
% 1.58/0.57  fof(f171,plain,(
% 1.58/0.57    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f170,f67])).
% 1.58/0.57  fof(f170,plain,(
% 1.58/0.57    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f169,f68])).
% 1.58/0.57  fof(f169,plain,(
% 1.58/0.57    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f150,f160])).
% 1.58/0.57  fof(f160,plain,(
% 1.58/0.57    v3_pre_topc(u1_struct_0(sK3),sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f159,f67])).
% 1.58/0.57  fof(f159,plain,(
% 1.58/0.57    v3_pre_topc(u1_struct_0(sK3),sK1) | ~v2_pre_topc(sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f158,f68])).
% 1.58/0.57  fof(f158,plain,(
% 1.58/0.57    v3_pre_topc(u1_struct_0(sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f157,f73])).
% 1.58/0.57  fof(f73,plain,(
% 1.58/0.57    v1_tsep_1(sK3,sK1)),
% 1.58/0.57    inference(cnf_transformation,[],[f47])).
% 1.58/0.57  fof(f157,plain,(
% 1.58/0.57    ~v1_tsep_1(sK3,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f146,f74])).
% 1.58/0.57  fof(f146,plain,(
% 1.58/0.57    ~m1_pre_topc(sK3,sK1) | ~v1_tsep_1(sK3,sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.58/0.57    inference(resolution,[],[f132,f114])).
% 1.58/0.57  fof(f114,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f109])).
% 1.58/0.57  fof(f109,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.57    inference(equality_resolution,[],[f94])).
% 1.58/0.57  fof(f94,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f55])).
% 1.58/0.57  fof(f55,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.57    inference(flattening,[],[f54])).
% 1.58/0.57  fof(f54,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.57    inference(nnf_transformation,[],[f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.58/0.57    inference(flattening,[],[f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,axiom,(
% 1.58/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.58/0.57  fof(f132,plain,(
% 1.58/0.57    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.58/0.57    inference(subsumption_resolution,[],[f128,f68])).
% 1.58/0.57  fof(f128,plain,(
% 1.58/0.57    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.58/0.57    inference(resolution,[],[f74,f81])).
% 1.58/0.57  fof(f81,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.58/0.57  fof(f150,plain,(
% 1.58/0.57    ( ! [X2] : (~r2_hidden(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | r1_tarski(sK7(sK1,u1_struct_0(sK3),X2),u1_struct_0(sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f132,f84])).
% 1.58/0.57  fof(f84,plain,(
% 1.58/0.57    ( ! [X4,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | r1_tarski(sK7(X0,X1,X4),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f52])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK6(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK7(X0,X1,X4),X1) & m1_connsp_2(sK7(X0,X1,X4),X0,X4) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK6(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK7(X0,X1,X4),X1) & m1_connsp_2(sK7(X0,X1,X4),X0,X4) & m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f49,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(rectify,[],[f48])).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(nnf_transformation,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/0.57    inference(flattening,[],[f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 1.58/0.57  fof(f629,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0)) | sP10(X0,sK1,sK4)) ) | ~spl12_15),
% 1.58/0.57    inference(subsumption_resolution,[],[f628,f75])).
% 1.58/0.57  fof(f628,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | sP10(X0,sK1,sK4)) ) | ~spl12_15),
% 1.58/0.57    inference(subsumption_resolution,[],[f627,f365])).
% 1.58/0.57  fof(f627,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(sK4,u1_struct_0(sK3)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),sK4),u1_struct_0(X0)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | sP10(X0,sK1,sK4)) ) | ~spl12_15),
% 1.58/0.57    inference(resolution,[],[f340,f325])).
% 1.58/0.57  fof(f325,plain,(
% 1.58/0.57    m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4) | ~spl12_15),
% 1.58/0.57    inference(avatar_component_clause,[],[f323])).
% 1.58/0.57  fof(f323,plain,(
% 1.58/0.57    spl12_15 <=> m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 1.58/0.57  fof(f340,plain,(
% 1.58/0.57    ( ! [X12,X10,X11] : (~m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X10),sK1,X12) | ~r2_hidden(X10,u1_struct_0(sK3)) | ~r1_tarski(sK7(sK1,u1_struct_0(sK3),X10),u1_struct_0(X11)) | ~m1_subset_1(X10,u1_struct_0(sK1)) | sP10(X11,sK1,X12)) )),
% 1.58/0.57    inference(resolution,[],[f164,f110])).
% 1.58/0.57  fof(f164,plain,(
% 1.58/0.57    ( ! [X0] : (m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK3))) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f163,f66])).
% 1.58/0.57  fof(f163,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f162,f67])).
% 1.58/0.57  fof(f162,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f161,f68])).
% 1.58/0.57  fof(f161,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f148,f160])).
% 1.58/0.57  fof(f148,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | m1_subset_1(sK7(sK1,u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f132,f82])).
% 1.58/0.57  fof(f82,plain,(
% 1.58/0.57    ( ! [X4,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | m1_subset_1(sK7(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f52])).
% 1.58/0.57  fof(f367,plain,(
% 1.58/0.57    spl12_16),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f366])).
% 1.58/0.57  fof(f366,plain,(
% 1.58/0.57    $false | spl12_16),
% 1.58/0.57    inference(subsumption_resolution,[],[f365,f329])).
% 1.58/0.57  fof(f329,plain,(
% 1.58/0.57    ~r2_hidden(sK4,u1_struct_0(sK3)) | spl12_16),
% 1.58/0.57    inference(avatar_component_clause,[],[f327])).
% 1.58/0.57  fof(f327,plain,(
% 1.58/0.57    spl12_16 <=> r2_hidden(sK4,u1_struct_0(sK3))),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 1.58/0.57  fof(f330,plain,(
% 1.58/0.57    spl12_15 | ~spl12_16),
% 1.58/0.57    inference(avatar_split_clause,[],[f321,f327,f323])).
% 1.58/0.57  fof(f321,plain,(
% 1.58/0.57    ~r2_hidden(sK4,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),sK4),sK1,sK4)),
% 1.58/0.57    inference(resolution,[],[f168,f75])).
% 1.58/0.57  fof(f168,plain,(
% 1.58/0.57    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_hidden(X1,u1_struct_0(sK3)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f167,f66])).
% 1.58/0.57  fof(f167,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f166,f67])).
% 1.58/0.57  fof(f166,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f165,f68])).
% 1.58/0.57  fof(f165,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f149,f160])).
% 1.58/0.57  fof(f149,plain,(
% 1.58/0.57    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | m1_connsp_2(sK7(sK1,u1_struct_0(sK3),X1),sK1,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.58/0.57    inference(resolution,[],[f132,f83])).
% 1.58/0.57  fof(f83,plain,(
% 1.58/0.57    ( ! [X4,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | m1_connsp_2(sK7(X0,X1,X4),X0,X4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f52])).
% 1.58/0.57  fof(f124,plain,(
% 1.58/0.57    spl12_1 | spl12_2),
% 1.58/0.57    inference(avatar_split_clause,[],[f78,f120,f116])).
% 1.58/0.57  fof(f78,plain,(
% 1.58/0.57    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.58/0.57    inference(cnf_transformation,[],[f47])).
% 1.58/0.57  fof(f123,plain,(
% 1.58/0.57    ~spl12_1 | ~spl12_2),
% 1.58/0.57    inference(avatar_split_clause,[],[f79,f120,f116])).
% 1.58/0.57  fof(f79,plain,(
% 1.58/0.57    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.58/0.57    inference(cnf_transformation,[],[f47])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (10855)------------------------------
% 1.58/0.57  % (10855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (10855)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (10855)Memory used [KB]: 11129
% 1.58/0.57  % (10855)Time elapsed: 0.169 s
% 1.58/0.57  % (10855)------------------------------
% 1.58/0.57  % (10855)------------------------------
% 1.58/0.57  % (10843)Success in time 0.206 s
%------------------------------------------------------------------------------
