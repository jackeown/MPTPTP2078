%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 844 expanded)
%              Number of leaves         :   31 ( 366 expanded)
%              Depth                    :   28
%              Number of atoms          : 1329 (13504 expanded)
%              Number of equality atoms :   40 ( 900 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f129,f230,f290,f294,f302,f324])).

fof(f324,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f322,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
      | ~ r1_tmap_1(sK5,sK4,sK6,sK8) )
    & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
      | r1_tmap_1(sK5,sK4,sK6,sK8) )
    & sK8 = sK9
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_pre_topc(sK7,sK5)
    & v1_tsep_1(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f46,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK4,X2,X4) )
                          & ( r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                            | r1_tmap_1(X1,sK4,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                          | ~ r1_tmap_1(X1,sK4,X2,X4) )
                        & ( r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                          | r1_tmap_1(X1,sK4,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_pre_topc(X3,X1)
                & v1_tsep_1(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5)
                        | ~ r1_tmap_1(sK5,sK4,X2,X4) )
                      & ( r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5)
                        | r1_tmap_1(sK5,sK4,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(sK5)) )
              & m1_pre_topc(X3,sK5)
              & v1_tsep_1(X3,sK5)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
          & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK4))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5)
                      | ~ r1_tmap_1(sK5,sK4,X2,X4) )
                    & ( r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5)
                      | r1_tmap_1(sK5,sK4,X2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(sK5)) )
            & m1_pre_topc(X3,sK5)
            & v1_tsep_1(X3,sK5)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK4))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5)
                    | ~ r1_tmap_1(sK5,sK4,sK6,X4) )
                  & ( r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5)
                    | r1_tmap_1(sK5,sK4,sK6,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(sK5)) )
          & m1_pre_topc(X3,sK5)
          & v1_tsep_1(X3,sK5)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5)
                  | ~ r1_tmap_1(sK5,sK4,sK6,X4) )
                & ( r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5)
                  | r1_tmap_1(sK5,sK4,sK6,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_subset_1(X4,u1_struct_0(sK5)) )
        & m1_pre_topc(X3,sK5)
        & v1_tsep_1(X3,sK5)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
                | ~ r1_tmap_1(sK5,sK4,sK6,X4) )
              & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
                | r1_tmap_1(sK5,sK4,sK6,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(sK7)) )
          & m1_subset_1(X4,u1_struct_0(sK5)) )
      & m1_pre_topc(sK7,sK5)
      & v1_tsep_1(sK7,sK5)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
              | ~ r1_tmap_1(sK5,sK4,sK6,X4) )
            & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
              | r1_tmap_1(sK5,sK4,sK6,X4) )
            & X4 = X5
            & m1_subset_1(X5,u1_struct_0(sK7)) )
        & m1_subset_1(X4,u1_struct_0(sK5)) )
   => ( ? [X5] :
          ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
            | ~ r1_tmap_1(sK5,sK4,sK6,sK8) )
          & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
            | r1_tmap_1(sK5,sK4,sK6,sK8) )
          & sK8 = X5
          & m1_subset_1(X5,u1_struct_0(sK7)) )
      & m1_subset_1(sK8,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X5] :
        ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
          | ~ r1_tmap_1(sK5,sK4,sK6,sK8) )
        & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5)
          | r1_tmap_1(sK5,sK4,sK6,sK8) )
        & sK8 = X5
        & m1_subset_1(X5,u1_struct_0(sK7)) )
   => ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
        | ~ r1_tmap_1(sK5,sK4,sK6,sK8) )
      & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
        | r1_tmap_1(sK5,sK4,sK6,sK8) )
      & sK8 = sK9
      & m1_subset_1(sK9,u1_struct_0(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f322,plain,
    ( v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f321,f70])).

fof(f70,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f321,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f320,f71])).

fof(f71,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f319,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f319,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f318,f73])).

fof(f73,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f318,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f317,f74])).

fof(f74,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f316,f75])).

fof(f75,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f316,plain,
    ( ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f315,f76])).

fof(f76,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f53])).

fof(f315,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f314,f77])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f314,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f313,f78])).

fof(f78,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f313,plain,
    ( v2_struct_0(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f312,f80])).

fof(f80,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f312,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f311,f130])).

fof(f130,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(forward_demodulation,[],[f82,f83])).

fof(f83,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f311,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ spl12_1
    | spl12_2 ),
    inference(subsumption_resolution,[],[f310,f122])).

fof(f122,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK8)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl12_1
  <=> r1_tmap_1(sK5,sK4,sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f310,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK7,sK5)
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl12_2 ),
    inference(resolution,[],[f303,f204])).

fof(f204,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
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
    inference(subsumption_resolution,[],[f114,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f114,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
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
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f303,plain,
    ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK8)
    | spl12_2 ),
    inference(forward_demodulation,[],[f127,f83])).

fof(f127,plain,
    ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl12_2
  <=> r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f302,plain,(
    spl12_10 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl12_10 ),
    inference(subsumption_resolution,[],[f300,f79])).

fof(f79,plain,(
    v1_tsep_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f300,plain,
    ( ~ v1_tsep_1(sK7,sK5)
    | spl12_10 ),
    inference(subsumption_resolution,[],[f299,f80])).

fof(f299,plain,
    ( ~ m1_pre_topc(sK7,sK5)
    | ~ v1_tsep_1(sK7,sK5)
    | spl12_10 ),
    inference(resolution,[],[f298,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f298,plain,
    ( ~ sP2(sK5,sK7)
    | spl12_10 ),
    inference(subsumption_resolution,[],[f297,f74])).

fof(f297,plain,
    ( ~ sP2(sK5,sK7)
    | ~ l1_pre_topc(sK5)
    | spl12_10 ),
    inference(subsumption_resolution,[],[f296,f73])).

fof(f296,plain,
    ( ~ v2_pre_topc(sK5)
    | ~ sP2(sK5,sK7)
    | ~ l1_pre_topc(sK5)
    | spl12_10 ),
    inference(resolution,[],[f289,f182])).

fof(f182,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(u1_struct_0(X2),X3)
      | ~ v2_pre_topc(X3)
      | ~ sP2(X3,X2)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f181,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f181,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ sP2(X3,X2)
      | v3_pre_topc(u1_struct_0(X2),X3) ) ),
    inference(resolution,[],[f179,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X0,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP2(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP2(X0,X2) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP2(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP2(X0,X1) ) )
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( sP2(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sP3(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f117,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
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

fof(f117,plain,(
    ! [X0,X1] :
      ( sP3(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f31,f43,f42])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f289,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl12_10
  <=> v3_pre_topc(u1_struct_0(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f294,plain,
    ( spl12_7
    | spl12_9 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl12_7
    | spl12_9 ),
    inference(subsumption_resolution,[],[f292,f130])).

fof(f292,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | spl12_7
    | spl12_9 ),
    inference(subsumption_resolution,[],[f291,f168])).

fof(f168,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK7))
    | spl12_7 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl12_7
  <=> v1_xboole_0(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f291,plain,
    ( v1_xboole_0(u1_struct_0(sK7))
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | spl12_9 ),
    inference(resolution,[],[f285,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f285,plain,
    ( ~ r2_hidden(sK8,u1_struct_0(sK7))
    | spl12_9 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl12_9
  <=> r2_hidden(sK8,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f290,plain,
    ( ~ spl12_9
    | ~ spl12_10
    | spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f281,f125,f121,f287,f283])).

fof(f281,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ r2_hidden(sK8,u1_struct_0(sK7))
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f280,f80])).

fof(f280,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ r2_hidden(sK8,u1_struct_0(sK7))
    | ~ m1_pre_topc(sK7,sK5)
    | spl12_1
    | ~ spl12_2 ),
    inference(resolution,[],[f277,f118])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f277,plain,
    ( ! [X2] :
        ( ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK7))
        | ~ v3_pre_topc(u1_struct_0(X2),sK5)
        | ~ r2_hidden(sK8,u1_struct_0(X2))
        | ~ m1_pre_topc(X2,sK5) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f272,f74])).

fof(f272,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK8,u1_struct_0(X2))
        | ~ v3_pre_topc(u1_struct_0(X2),sK5)
        | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(sK7))
        | ~ m1_pre_topc(X2,sK5)
        | ~ l1_pre_topc(sK5) )
    | spl12_1
    | ~ spl12_2 ),
    inference(resolution,[],[f270,f87])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK7)) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f269,f69])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f268,f70])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f267,f71])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f266,f72])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f265,f73])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f264,f74])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f263,f75])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f262,f76])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f261,f77])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f260,f78])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f259,f80])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f258,f130])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(sK8,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f255,f123])).

fof(f123,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f255,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK5,sK4,sK6,sK8)
        | ~ r1_tarski(X0,u1_struct_0(sK7))
        | ~ r2_hidden(sK8,X0)
        | ~ v3_pre_topc(X0,sK5)
        | ~ m1_subset_1(sK8,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ m1_pre_topc(sK7,sK5)
        | v2_struct_0(sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
        | ~ v1_funct_1(sK6)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4) )
    | ~ spl12_2 ),
    inference(resolution,[],[f243,f131])).

fof(f131,plain,
    ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK8)
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f126,f83])).

fof(f126,plain,
    ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f243,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
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
    inference(subsumption_resolution,[],[f115,f99])).

fof(f115,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
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
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f230,plain,(
    ~ spl12_7 ),
    inference(avatar_split_clause,[],[f226,f167])).

fof(f226,plain,(
    ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f225,f136])).

fof(f136,plain,(
    v2_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f135,f73])).

fof(f135,plain,
    ( v2_pre_topc(sK7)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f134,f74])).

fof(f134,plain,
    ( v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f225,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f224,f133])).

fof(f133,plain,(
    l1_pre_topc(sK7) ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f132,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[],[f86,f80])).

fof(f86,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f224,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f216,f78])).

fof(f216,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ v1_xboole_0(u1_struct_0(sK7)) ),
    inference(resolution,[],[f214,f130])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f212,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK11(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK11(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f37,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK11(X0,X1),X0,X1) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f211,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X2,X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ sP0(X1,X2,X0)
      | ~ sP0(X1,X2,X0) ) ),
    inference(resolution,[],[f151,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK10(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( r2_hidden(X0,sK10(X0,X1,X2))
          & r1_tarski(sK10(X0,X1,X2),X1)
          & v3_pre_topc(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X0,sK10(X0,X1,X2))
        & r1_tarski(sK10(X0,X1,X2),X1)
        & v3_pre_topc(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( r2_hidden(X0,X4)
            & r1_tarski(X4,X1)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X1,X3)
            | ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( r2_hidden(X1,X3)
            & r1_tarski(X3,X2)
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,sK10(X0,X1,X2))
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f90,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X2,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X2,X1,X0)
      | ~ m1_connsp_2(X2,X1,X0)
      | sP0(X0,X2,X1) ) ),
    inference(condensation,[],[f209])).

fof(f209,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_connsp_2(X6,X5,X4)
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_connsp_2(X6,X5,X7)
      | sP0(X7,X6,X5) ) ),
    inference(resolution,[],[f191,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ m1_connsp_2(X1,X0,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_connsp_2(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ m1_connsp_2(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( m1_connsp_2(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ m1_connsp_2(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( m1_connsp_2(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X0,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | sP1(X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f108,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f40,f39])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f129,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f84,f125,f121])).

fof(f84,plain,
    ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | r1_tmap_1(sK5,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f128,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f85,f125,f121])).

fof(f85,plain,
    ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | ~ r1_tmap_1(sK5,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (5434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.47  % (5445)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (5442)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (5453)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.48  % (5434)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f128,f129,f230,f290,f294,f302,f324])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ~spl12_1 | spl12_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    $false | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f322,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v2_struct_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ((((((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~r1_tmap_1(sK5,sK4,sK6,sK8)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | r1_tmap_1(sK5,sK4,sK6,sK8)) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_pre_topc(sK7,sK5) & v1_tsep_1(sK7,sK5) & ~v2_struct_0(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f46,f52,f51,f50,f49,f48,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | ~r1_tmap_1(X1,sK4,X2,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | r1_tmap_1(X1,sK4,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | ~r1_tmap_1(X1,sK4,X2,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | r1_tmap_1(X1,sK4,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5) | ~r1_tmap_1(sK5,sK4,X2,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5) | r1_tmap_1(sK5,sK4,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5) | ~r1_tmap_1(sK5,sK4,X2,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,X2,X3),X5) | r1_tmap_1(sK5,sK4,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5) | ~r1_tmap_1(sK5,sK4,sK6,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5) | r1_tmap_1(sK5,sK4,sK6,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK6))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5) | ~r1_tmap_1(sK5,sK4,sK6,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(sK5,sK4,sK6,X3),X5) | r1_tmap_1(sK5,sK4,sK6,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | ~r1_tmap_1(sK5,sK4,sK6,X4)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | r1_tmap_1(sK5,sK4,sK6,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK7))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(sK7,sK5) & v1_tsep_1(sK7,sK5) & ~v2_struct_0(sK7))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ? [X4] : (? [X5] : ((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | ~r1_tmap_1(sK5,sK4,sK6,X4)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | r1_tmap_1(sK5,sK4,sK6,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK7))) & m1_subset_1(X4,u1_struct_0(sK5))) => (? [X5] : ((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | ~r1_tmap_1(sK5,sK4,sK6,sK8)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | r1_tmap_1(sK5,sK4,sK6,sK8)) & sK8 = X5 & m1_subset_1(X5,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK5)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ? [X5] : ((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | ~r1_tmap_1(sK5,sK4,sK6,sK8)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X5) | r1_tmap_1(sK5,sK4,sK6,sK8)) & sK8 = X5 & m1_subset_1(X5,u1_struct_0(sK7))) => ((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~r1_tmap_1(sK5,sK4,sK6,sK8)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | r1_tmap_1(sK5,sK4,sK6,sK8)) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK7)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f321,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v2_pre_topc(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f320,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    l1_pre_topc(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f319,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ~v2_struct_0(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f318,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    v2_pre_topc(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f317,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    l1_pre_topc(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f316,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    v1_funct_1(sK6)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f315,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f314,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f313,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~v2_struct_0(sK7)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f312,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    m1_pre_topc(sK7,sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f311,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    m1_subset_1(sK8,u1_struct_0(sK7))),
% 0.21/0.48    inference(forward_demodulation,[],[f82,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    sK8 = sK9),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    m1_subset_1(sK9,u1_struct_0(sK7))),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    ~m1_subset_1(sK8,u1_struct_0(sK7)) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | (~spl12_1 | spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f310,f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    r1_tmap_1(sK5,sK4,sK6,sK8) | ~spl12_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl12_1 <=> r1_tmap_1(sK5,sK4,sK6,sK8)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    ~r1_tmap_1(sK5,sK4,sK6,sK8) | ~m1_subset_1(sK8,u1_struct_0(sK7)) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl12_2),
% 0.21/0.48    inference(resolution,[],[f303,f204])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    ~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK8) | spl12_2),
% 0.21/0.48    inference(forward_demodulation,[],[f127,f83])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | spl12_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl12_2 <=> r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    spl12_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f301])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    $false | spl12_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f300,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    v1_tsep_1(sK7,sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    ~v1_tsep_1(sK7,sK5) | spl12_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f299,f80])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    ~m1_pre_topc(sK7,sK5) | ~v1_tsep_1(sK7,sK5) | spl12_10),
% 0.21/0.48    inference(resolution,[],[f298,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP2(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP2(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP2(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP2(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP2(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1] : (sP2(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    ~sP2(sK5,sK7) | spl12_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f297,f74])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    ~sP2(sK5,sK7) | ~l1_pre_topc(sK5) | spl12_10),
% 0.21/0.48    inference(subsumption_resolution,[],[f296,f73])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    ~v2_pre_topc(sK5) | ~sP2(sK5,sK7) | ~l1_pre_topc(sK5) | spl12_10),
% 0.21/0.48    inference(resolution,[],[f289,f182])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ( ! [X2,X3] : (v3_pre_topc(u1_struct_0(X2),X3) | ~v2_pre_topc(X3) | ~sP2(X3,X2) | ~l1_pre_topc(X3)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP2(X0,X1) | m1_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f64])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~sP2(X3,X2) | v3_pre_topc(u1_struct_0(X2),X3)) )),
% 0.21/0.48    inference(resolution,[],[f179,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~sP2(X0,X2) | v3_pre_topc(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((sP2(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP2(X0,X2))) | ~sP3(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (((sP2(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP2(X0,X1))) | ~sP3(X0,X2,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((sP2(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP3(X0,X2,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP3(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP3(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (sP3(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(definition_folding,[],[f31,f43,f42])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ~v3_pre_topc(u1_struct_0(sK7),sK5) | spl12_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f287])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl12_10 <=> v3_pre_topc(u1_struct_0(sK7),sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    spl12_7 | spl12_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f293])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    $false | (spl12_7 | spl12_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f292,f130])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ~m1_subset_1(sK8,u1_struct_0(sK7)) | (spl12_7 | spl12_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f291,f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK7)) | spl12_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f167])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl12_7 <=> v1_xboole_0(u1_struct_0(sK7))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK7)) | ~m1_subset_1(sK8,u1_struct_0(sK7)) | spl12_9),
% 0.21/0.48    inference(resolution,[],[f285,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~r2_hidden(sK8,u1_struct_0(sK7)) | spl12_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f283])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    spl12_9 <=> r2_hidden(sK8,u1_struct_0(sK7))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    ~spl12_9 | ~spl12_10 | spl12_1 | ~spl12_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f281,f125,f121,f287,f283])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ~v3_pre_topc(u1_struct_0(sK7),sK5) | ~r2_hidden(sK8,u1_struct_0(sK7)) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f280,f80])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    ~v3_pre_topc(u1_struct_0(sK7),sK5) | ~r2_hidden(sK8,u1_struct_0(sK7)) | ~m1_pre_topc(sK7,sK5) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(resolution,[],[f277,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ( ! [X2] : (~r1_tarski(u1_struct_0(X2),u1_struct_0(sK7)) | ~v3_pre_topc(u1_struct_0(X2),sK5) | ~r2_hidden(sK8,u1_struct_0(X2)) | ~m1_pre_topc(X2,sK5)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f272,f74])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(sK8,u1_struct_0(X2)) | ~v3_pre_topc(u1_struct_0(X2),sK5) | ~r1_tarski(u1_struct_0(X2),u1_struct_0(sK7)) | ~m1_pre_topc(X2,sK5) | ~l1_pre_topc(sK5)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(resolution,[],[f270,f87])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~r1_tarski(X0,u1_struct_0(sK7))) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f269,f69])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f268,f70])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f267,f71])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f266,f72])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f265,f73])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f74])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f263,f75])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f262,f76])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f261,f77])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f78])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f259,f80])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f258,f130])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(sK8,u1_struct_0(sK7)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | (spl12_1 | ~spl12_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~r1_tmap_1(sK5,sK4,sK6,sK8) | spl12_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tmap_1(sK5,sK4,sK6,sK8) | ~r1_tarski(X0,u1_struct_0(sK7)) | ~r2_hidden(sK8,X0) | ~v3_pre_topc(X0,sK5) | ~m1_subset_1(sK8,u1_struct_0(sK7)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_pre_topc(sK7,sK5) | v2_struct_0(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5) | v2_struct_0(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) ) | ~spl12_2),
% 0.21/0.48    inference(resolution,[],[f243,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK8) | ~spl12_2),
% 0.21/0.48    inference(forward_demodulation,[],[f126,f83])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~spl12_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f99])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~spl12_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f226,f167])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK7))),
% 0.21/0.48    inference(subsumption_resolution,[],[f225,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    v2_pre_topc(sK7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f73])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    v2_pre_topc(sK7) | ~v2_pre_topc(sK5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f74])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    v2_pre_topc(sK7) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 0.21/0.48    inference(resolution,[],[f100,f80])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~v2_pre_topc(sK7) | ~v1_xboole_0(u1_struct_0(sK7))),
% 0.21/0.48    inference(subsumption_resolution,[],[f224,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    l1_pre_topc(sK7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f74])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    l1_pre_topc(sK7) | ~l1_pre_topc(sK5)),
% 0.21/0.48    inference(resolution,[],[f86,f80])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~v1_xboole_0(u1_struct_0(sK7))),
% 0.21/0.48    inference(subsumption_resolution,[],[f216,f78])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | ~v1_xboole_0(u1_struct_0(sK7))),
% 0.21/0.48    inference(resolution,[],[f214,f130])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f213])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f212,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_connsp_2(sK11(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_connsp_2(sK11(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f37,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK11(X0,X1),X0,X1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.48    inference(resolution,[],[f211,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP0(X1,X2,X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(u1_struct_0(X0)) | ~sP0(X1,X2,X0) | ~sP0(X1,X2,X0)) )),
% 0.21/0.48    inference(resolution,[],[f151,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,sK10(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK10(X0,X1,X2)) & r1_tarski(sK10(X0,X1,X2),X1) & v3_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f57,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK10(X0,X1,X2)) & r1_tarski(sK10(X0,X1,X2),X1) & v3_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,sK10(X0,X1,X2)) | ~v1_xboole_0(u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f90,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f59])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X2,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f210])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X2,X1,X0) | ~m1_connsp_2(X2,X1,X0) | sP0(X0,X2,X1)) )),
% 0.21/0.48    inference(condensation,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_connsp_2(X6,X5,X4) | ~m1_subset_1(X7,u1_struct_0(X5)) | ~m1_connsp_2(X6,X5,X7) | sP0(X7,X6,X5)) )),
% 0.21/0.48    inference(resolution,[],[f191,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~m1_connsp_2(X1,X0,X2) | sP0(X2,X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((m1_connsp_2(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~m1_connsp_2(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (((m1_connsp_2(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~m1_connsp_2(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((m1_connsp_2(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP1(X1,X0,X3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_connsp_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | sP1(X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f108,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(definition_folding,[],[f21,f40,f39])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl12_1 | spl12_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f125,f121])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | r1_tmap_1(sK5,sK4,sK6,sK8)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~spl12_1 | ~spl12_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f85,f125,f121])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~r1_tmap_1(sK5,sK4,sK6,sK8)),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5434)------------------------------
% 0.21/0.48  % (5434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5434)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5434)Memory used [KB]: 6396
% 0.21/0.48  % (5434)Time elapsed: 0.068 s
% 0.21/0.48  % (5434)------------------------------
% 0.21/0.48  % (5434)------------------------------
% 0.21/0.48  % (5429)Success in time 0.12 s
%------------------------------------------------------------------------------
