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
% DateTime   : Thu Dec  3 13:18:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  192 (2111 expanded)
%              Number of leaves         :   24 ( 919 expanded)
%              Depth                    :   40
%              Number of atoms          : 1426 (35238 expanded)
%              Number of equality atoms :   46 (2382 expanded)
%              Maximal formula depth    :   28 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f803,plain,(
    $false ),
    inference(subsumption_resolution,[],[f802,f222])).

fof(f222,plain,(
    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f221,f73])).

fof(f73,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
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

% (30284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f20])).

% (30288)Refutation not found, incomplete strategy% (30288)------------------------------
% (30288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30288)Termination reason: Refutation not found, incomplete strategy

% (30288)Memory used [KB]: 6268
% (30288)Time elapsed: 0.119 s
% (30288)------------------------------
% (30288)------------------------------
fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f221,plain,
    ( r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f220,f134])).

fof(f134,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f133,f68])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f133,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f132,f69])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f93,f75])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f220,plain,
    ( r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f219,f129])).

fof(f129,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f128,f69])).

fof(f128,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f81,f75])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f219,plain,
    ( r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f206,f119])).

fof(f119,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f77,f78])).

fof(f78,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f206,plain,
    ( r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f182,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f88,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f182,plain,(
    m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4) ),
    inference(subsumption_resolution,[],[f181,f73])).

fof(f181,plain,
    ( m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f180,f134])).

fof(f180,plain,
    ( m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f176,f129])).

fof(f176,plain,
    ( m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f174,f119])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,X1,sK7(X0,X1)),X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,sK7(X0,X1)),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f124,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_connsp_2(sK6(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f85,f99])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK6(X0,X1,X2),X2)
                & v3_pre_topc(sK6(X0,X1,X2),X0)
                & m1_connsp_2(sK6(X0,X1,X2),X0,X1)
                & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK6(X0,X1,X2),X2)
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_connsp_2(sK6(X0,X1,X2),X0,X1)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f802,plain,(
    ~ r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) ),
    inference(subsumption_resolution,[],[f789,f226])).

fof(f226,plain,(
    r1_tarski(sK6(sK3,sK4,sK7(sK3,sK4)),u1_struct_0(sK3)) ),
    inference(resolution,[],[f218,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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

fof(f218,plain,(
    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f217,f73])).

fof(f217,plain,
    ( m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f216,f134])).

fof(f216,plain,
    ( m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f215,f129])).

fof(f215,plain,
    ( m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f205,f119])).

fof(f205,plain,
    ( m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f182,f99])).

fof(f789,plain,
    ( ~ r1_tarski(sK6(sK3,sK4,sK7(sK3,sK4)),u1_struct_0(sK3))
    | ~ r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) ),
    inference(resolution,[],[f786,f557])).

fof(f557,plain,(
    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) ),
    inference(subsumption_resolution,[],[f556,f73])).

fof(f556,plain,
    ( v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f555,f134])).

fof(f555,plain,
    ( v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f554,f129])).

fof(f554,plain,
    ( v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f553,f119])).

fof(f553,plain,
    ( v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f546,f218])).

fof(f546,plain,
    ( v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)
    | ~ m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f545,f100])).

fof(f545,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK4)
      | v3_pre_topc(sK6(sK3,sK4,X0),sK1)
      | ~ m1_subset_1(sK6(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f535,f119])).

fof(f535,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | v3_pre_topc(sK6(sK3,X1,X2),sK1)
      | ~ m1_connsp_2(X2,sK3,X1)
      | ~ m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f534,f73])).

fof(f534,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(sK6(sK3,X1,X2),sK1)
      | ~ m1_connsp_2(X2,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f533,f134])).

fof(f533,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(sK6(sK3,X1,X2),sK1)
      | ~ m1_connsp_2(X2,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f530,f129])).

fof(f530,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(sK6(sK3,X1,X2),sK1)
      | ~ m1_connsp_2(X2,sK3,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f527,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f99])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f527,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f526,f104])).

fof(f526,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f525,f75])).

fof(f525,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f524,f114])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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

fof(f524,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ m1_pre_topc(sK3,sK1)
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f402,f74])).

fof(f74,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f402,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,sK1)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X1,sK1)
      | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f401,f68])).

fof(f401,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X1,sK1)
      | ~ v1_tsep_1(X1,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f399,f69])).

fof(f399,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1)
      | ~ m1_pre_topc(X1,sK1)
      | ~ v1_tsep_1(X1,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f398,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f116,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f94])).

% (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30289)Termination reason: Refutation not found, incomplete strategy

% (30289)Memory used [KB]: 10746
% (30289)Time elapsed: 0.089 s
% (30289)------------------------------
% (30289)------------------------------
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f398,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f397,f141])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f140,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f139,f69])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f83,f75])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f396,f68])).

fof(f396,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X0,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f395,f69])).

fof(f395,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f122,f75])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ r1_tarski(X4,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X4,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f113,f83])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( v3_pre_topc(X4,X0)
      | ~ v3_pre_topc(X4,X1)
      | ~ r1_tarski(X4,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ v3_pre_topc(X4,X1)
      | X3 != X4
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( v3_pre_topc(X4,X1)
                          | ~ v3_pre_topc(X3,X0) )
                        & ( v3_pre_topc(X3,X0)
                          | ~ v3_pre_topc(X4,X1) ) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( v3_pre_topc(X4,X1)
                      <=> v3_pre_topc(X3,X0) )
                      | X3 != X4
                      | ~ r1_tarski(X3,X2)
                      | ~ r1_tarski(X2,u1_struct_0(X1))
                      | ~ v3_pre_topc(X2,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( X3 = X4
                          & r1_tarski(X3,X2)
                          & r1_tarski(X2,u1_struct_0(X1))
                          & v3_pre_topc(X2,X0) )
                       => ( v3_pre_topc(X4,X1)
                        <=> v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tsep_1)).

fof(f786,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ r2_hidden(sK4,X1) ) ),
    inference(subsumption_resolution,[],[f785,f771])).

fof(f771,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | r1_tmap_1(sK1,sK0,sK2,sK4) ) ),
    inference(resolution,[],[f770,f117])).

fof(f117,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(backward_demodulation,[],[f79,f78])).

fof(f79,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f770,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f769,f118])).

fof(f118,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(backward_demodulation,[],[f80,f78])).

fof(f80,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f769,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ r2_hidden(sK4,X0)
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
      | r1_tmap_1(sK1,sK0,sK2,sK4) ) ),
    inference(resolution,[],[f768,f119])).

fof(f768,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f767,f141])).

fof(f767,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f766,f73])).

fof(f766,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | v2_struct_0(sK3)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0)
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(resolution,[],[f646,f75])).

fof(f646,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,sK1)
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2) ) ),
    inference(subsumption_resolution,[],[f645,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f645,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f644,f65])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f644,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f643,f66])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f643,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f642,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f642,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f641,f68])).

fof(f641,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f640,f69])).

fof(f640,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f639,f72])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f639,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r2_hidden(X2,X0)
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2)
      | r1_tmap_1(sK1,sK0,sK2,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f544,f71])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f544,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
      | ~ r1_tarski(X4,u1_struct_0(X0))
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
      | r1_tmap_1(X2,X1,sK2,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f543,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f543,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
      | ~ r1_tarski(X4,u1_struct_0(X0))
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X0,X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
      | r1_tmap_1(X2,X1,sK2,X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f107,f70])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
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
      | r1_tmap_1(X1,X0,X2,X6)
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
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f785,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ) ),
    inference(subsumption_resolution,[],[f784,f64])).

fof(f784,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f783,f65])).

fof(f783,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f782,f66])).

fof(f782,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f781,f67])).

% (30308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f781,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f780,f68])).

fof(f780,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f779,f69])).

fof(f779,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f778,f70])).

fof(f778,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f777,f71])).

fof(f777,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f776,f72])).

fof(f776,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f775,f73])).

fof(f775,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
      | v2_struct_0(sK3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ v1_funct_1(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f774,f75])).

fof(f774,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
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
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f773,f76])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f773,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
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
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f772,f119])).

fof(f772,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ v3_pre_topc(X1,sK1)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
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
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f770,f106])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f89])).

% (30296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (30283)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (30301)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (30286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (30285)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (30292)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (30295)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (30305)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (30299)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (30298)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (30294)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (30290)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (30293)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (30289)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (30283)Refutation not found, incomplete strategy% (30283)------------------------------
% 0.21/0.52  % (30283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30283)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30283)Memory used [KB]: 10746
% 0.21/0.52  % (30283)Time elapsed: 0.103 s
% 0.21/0.52  % (30283)------------------------------
% 0.21/0.52  % (30283)------------------------------
% 0.21/0.52  % (30302)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (30287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (30304)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (30286)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (30288)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (30300)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (30303)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f803,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f802,f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f221,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f51,f50,f49,f48,f47,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (30284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  % (30288)Refutation not found, incomplete strategy% (30288)------------------------------
% 0.21/0.53  % (30288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30288)Memory used [KB]: 6268
% 0.21/0.53  % (30288)Time elapsed: 0.119 s
% 0.21/0.53  % (30288)------------------------------
% 0.21/0.53  % (30288)------------------------------
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f220,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    v2_pre_topc(sK3) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f93,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f69])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.53    inference(resolution,[],[f81,f75])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.53    inference(forward_demodulation,[],[f77,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    sK4 = sK5),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f182,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f73])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f134])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f129])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    m1_connsp_2(sK6(sK3,sK4,sK7(sK3,sK4)),sK3,sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.53    inference(resolution,[],[f174,f119])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK6(X0,X1,sK7(X0,X1)),X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_connsp_2(sK6(X0,X1,sK7(X0,X1)),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(resolution,[],[f124,f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK7(X0,X1),X0,X1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_connsp_2(sK6(X0,X1,X2),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f99])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_connsp_2(sK6(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_connsp_2(sK6(X0,X1,X2),X0,X1) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK6(X0,X1,X2),X2) & v3_pre_topc(sK6(X0,X1,X2),X0) & m1_connsp_2(sK6(X0,X1,X2),X0,X1) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.54  fof(f802,plain,(
% 0.21/0.54    ~r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f789,f226])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    r1_tarski(sK6(sK3,sK4,sK7(sK3,sK4)),u1_struct_0(sK3))),
% 0.21/0.54    inference(resolution,[],[f218,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f217,f73])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f134])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f215,f129])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f205,f119])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f182,f99])).
% 0.21/0.54  fof(f789,plain,(
% 0.21/0.54    ~r1_tarski(sK6(sK3,sK4,sK7(sK3,sK4)),u1_struct_0(sK3)) | ~r2_hidden(sK4,sK6(sK3,sK4,sK7(sK3,sK4)))),
% 0.21/0.54    inference(resolution,[],[f786,f557])).
% 0.21/0.54  fof(f557,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1)),
% 0.21/0.54    inference(subsumption_resolution,[],[f556,f73])).
% 0.21/0.54  fof(f556,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f555,f134])).
% 0.21/0.54  fof(f555,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f554,f129])).
% 0.21/0.54  fof(f554,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f553,f119])).
% 0.21/0.54  fof(f553,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f546,f218])).
% 0.21/0.54  fof(f546,plain,(
% 0.21/0.54    v3_pre_topc(sK6(sK3,sK4,sK7(sK3,sK4)),sK1) | ~m1_subset_1(sK6(sK3,sK4,sK7(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.54    inference(resolution,[],[f545,f100])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK4) | v3_pre_topc(sK6(sK3,sK4,X0),sK1) | ~m1_subset_1(sK6(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.54    inference(resolution,[],[f535,f119])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | v3_pre_topc(sK6(sK3,X1,X2),sK1) | ~m1_connsp_2(X2,sK3,X1) | ~m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f534,f73])).
% 0.21/0.54  fof(f534,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(sK6(sK3,X1,X2),sK1) | ~m1_connsp_2(X2,sK3,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f533,f134])).
% 0.21/0.54  fof(f533,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(sK6(sK3,X1,X2),sK1) | ~m1_connsp_2(X2,sK3,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f530,f129])).
% 0.21/0.54  fof(f530,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~m1_subset_1(sK6(sK3,X1,X2),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(sK6(sK3,X1,X2),sK1) | ~m1_connsp_2(X2,sK3,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.54    inference(resolution,[],[f527,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f99])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(sK6(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f54])).
% 0.21/0.54  fof(f527,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f526,f104])).
% 0.21/0.54  fof(f526,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f525,f75])).
% 0.21/0.54  fof(f525,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~m1_pre_topc(sK3,sK1) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f524,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f524,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~m1_pre_topc(sK3,sK1) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f402,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    v1_tsep_1(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_tsep_1(X1,sK1) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK1) | ~r1_tarski(X0,u1_struct_0(X1))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f401,f68])).
% 0.21/0.54  fof(f401,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f399,f69])).
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1) | ~m1_pre_topc(X1,sK1) | ~v1_tsep_1(X1,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.54    inference(resolution,[],[f398,f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f116,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f94])).
% 0.21/0.54  % (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% 0.21/0.54  % (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30289)Memory used [KB]: 10746
% 0.21/0.54  % (30289)Time elapsed: 0.089 s
% 0.21/0.54  % (30289)------------------------------
% 0.21/0.54  % (30289)------------------------------
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(X1,sK1) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(X0,sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f397,f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.21/0.54    inference(resolution,[],[f140,f105])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f63])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f139,f69])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 0.21/0.54    inference(resolution,[],[f83,f75])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X0,sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f396,f68])).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X0,sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f395,f69])).
% 0.21/0.54  fof(f395,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.54    inference(resolution,[],[f122,f75])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v3_pre_topc(X4,X1) | ~r1_tarski(X4,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f83])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (v3_pre_topc(X4,X0) | ~v3_pre_topc(X4,X1) | ~r1_tarski(X4,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X1) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) | ~v3_pre_topc(X3,X0)) & (v3_pre_topc(X3,X0) | ~v3_pre_topc(X4,X1))) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0)) | (X3 != X4 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,u1_struct_0(X1)) | ~v3_pre_topc(X2,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ((X3 = X4 & r1_tarski(X3,X2) & r1_tarski(X2,u1_struct_0(X1)) & v3_pre_topc(X2,X0)) => (v3_pre_topc(X4,X1) <=> v3_pre_topc(X3,X0))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tsep_1)).
% 0.21/0.54  fof(f786,plain,(
% 0.21/0.54    ( ! [X1] : (~v3_pre_topc(X1,sK1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~r2_hidden(sK4,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f785,f771])).
% 0.21/0.54  fof(f771,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | r1_tmap_1(sK1,sK0,sK2,sK4)) )),
% 0.21/0.54    inference(resolution,[],[f770,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.54    inference(backward_demodulation,[],[f79,f78])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f770,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f769,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.54    inference(backward_demodulation,[],[f80,f78])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f769,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~r2_hidden(sK4,X0) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)) )),
% 0.21/0.54    inference(resolution,[],[f768,f119])).
% 0.21/0.54  fof(f768,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f767,f141])).
% 0.21/0.54  fof(f767,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f766,f73])).
% 0.21/0.54  fof(f766,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X1,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X0) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.54    inference(resolution,[],[f646,f75])).
% 0.21/0.54  fof(f646,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,sK1) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f645,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f645,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f644,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f644,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f643,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f643,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f642,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f642,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f641,f68])).
% 0.21/0.54  fof(f641,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f640,f69])).
% 0.21/0.54  fof(f640,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f639,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f639,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X2) | r1_tmap_1(sK1,sK0,sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f544,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~r1_tarski(X4,u1_struct_0(X0)) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3) | r1_tmap_1(X2,X1,sK2,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f543,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3) | ~r1_tarski(X4,u1_struct_0(X0)) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | r1_tmap_1(X2,X1,sK2,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.54    inference(resolution,[],[f107,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.21/0.54  fof(f785,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f784,f64])).
% 0.21/0.54  fof(f784,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f783,f65])).
% 0.21/0.54  fof(f783,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f782,f66])).
% 0.21/0.54  fof(f782,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f781,f67])).
% 0.21/0.54  % (30308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  fof(f781,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f780,f68])).
% 0.21/0.54  fof(f780,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f779,f69])).
% 0.21/0.54  fof(f779,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f778,f70])).
% 0.21/0.54  fof(f778,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f777,f71])).
% 0.21/0.54  fof(f777,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f776,f72])).
% 0.21/0.54  fof(f776,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f775,f73])).
% 0.21/0.54  fof(f775,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f774,f75])).
% 0.21/0.54  fof(f774,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f773,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f52])).
% 0.21/0.54  fof(f773,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f772,f119])).
% 0.21/0.54  fof(f772,plain,(
% 0.21/0.54    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_tarski(X1,u1_struct_0(sK3)) | ~v3_pre_topc(X1,sK1) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f770,f106])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f89])).
% 0.21/0.54  % (30296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (30286)------------------------------
% 0.21/0.54  % (30286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30286)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (30286)Memory used [KB]: 7036
% 0.21/0.54  % (30286)Time elapsed: 0.104 s
% 0.21/0.54  % (30286)------------------------------
% 0.21/0.54  % (30286)------------------------------
% 0.21/0.54  % (30277)Success in time 0.18 s
%------------------------------------------------------------------------------
