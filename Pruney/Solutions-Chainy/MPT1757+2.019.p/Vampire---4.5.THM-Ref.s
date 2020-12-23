%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 (1961 expanded)
%              Number of leaves         :   20 ( 833 expanded)
%              Depth                    :   45
%              Number of atoms          : 1182 (32405 expanded)
%              Number of equality atoms :   61 (2268 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f212,f105])).

fof(f105,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f104,f59])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f104,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f212,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f211,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f211,plain,(
    ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f210,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f210,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f209,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f209,plain,(
    v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f207,f194])).

fof(f194,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f193,f107])).

fof(f107,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f68,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f193,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f192,f160])).

fof(f160,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f159,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f158,f58])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f158,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f157,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f155,f66])).

fof(f66,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f155,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f153,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f153,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f152,f103])).

fof(f103,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f67,f68])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X0) ) ),
    inference(subsumption_resolution,[],[f151,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f110,f59])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f109,f63])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f151,plain,(
    ! [X0] :
      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f150,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK3))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(forward_demodulation,[],[f149,f132])).

fof(f132,plain,(
    u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f131,f65])).

fof(f131,plain,
    ( u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f130,f58])).

fof(f130,plain,
    ( u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(subsumption_resolution,[],[f129,f59])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK1)
    | u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1) ),
    inference(resolution,[],[f128,f64])).

fof(f64,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(condensation,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = k1_tops_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = k1_tops_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(condensation,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_tsep_1(X0,X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f123,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f99,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
      | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X0),X1)
      | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f121,f73])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) = X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X1,X0) = X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f81,f73])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X1,X3) = X3
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f149,plain,(
    ! [X0] :
      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,(
    ! [X0] :
      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f147,f58])).

fof(f147,plain,(
    ! [X0] :
      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3))) ) ),
    inference(subsumption_resolution,[],[f146,f59])).

fof(f146,plain,(
    ! [X0] :
      ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f119,f65])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_connsp_2(u1_struct_0(X2),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,k1_tops_1(X1,u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(X1,u1_struct_0(X2)))
      | m1_connsp_2(u1_struct_0(X2),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f76,f73])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f192,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f191,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f191,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f190,f153])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK1,sK4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ) ),
    inference(subsumption_resolution,[],[f189,f108])).

fof(f108,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f70,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(X0,sK1,sK4)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
      | r1_tmap_1(sK1,sK0,sK2,sK4) ) ),
    inference(resolution,[],[f188,f103])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f187,f63])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(X0,sK1,X1)
      | v2_struct_0(sK3)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(resolution,[],[f186,f65])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,sK1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(X0,sK1,X1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f185,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f55])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f56])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f182,f57])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f58])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f59])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f178,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f178,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_connsp_2(X4,X2,X3)
      | ~ r1_tarski(X4,u1_struct_0(X0))
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
    inference(resolution,[],[f177,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f177,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
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
    inference(subsumption_resolution,[],[f92,f80])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f207,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f206,f54])).

fof(f206,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f205,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f56])).

fof(f204,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f57])).

fof(f203,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f58])).

fof(f202,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f59])).

fof(f201,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f60])).

fof(f200,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f199,f61])).

fof(f199,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f63])).

fof(f197,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
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
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f196,f65])).

fof(f196,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
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
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f195,f103])).

fof(f195,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
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
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f193,f176])).

fof(f176,plain,(
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
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (6755)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (6764)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.47  % (6755)Refutation not found, incomplete strategy% (6755)------------------------------
% 0.21/0.47  % (6755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6764)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (6755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (6755)Memory used [KB]: 6524
% 0.21/0.47  % (6755)Time elapsed: 0.063 s
% 0.21/0.47  % (6755)------------------------------
% 0.21/0.47  % (6755)------------------------------
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f212,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    l1_pre_topc(sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    l1_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f46,f45,f44,f43,f42,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | ~r1_tmap_1(sK1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X5) | r1_tmap_1(sK1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ? [X4] : (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,X4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(sK1))) => (? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ? [X5] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f14])).
% 0.21/0.47  fof(f14,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 0.21/0.47    inference(resolution,[],[f72,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    m1_pre_topc(sK3,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    ~l1_pre_topc(sK3)),
% 0.21/0.47    inference(resolution,[],[f211,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ~l1_struct_0(sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f210,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~v2_struct_0(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.21/0.47    inference(resolution,[],[f209,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.47    inference(subsumption_resolution,[],[f207,f194])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    r1_tmap_1(sK1,sK0,sK2,sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.47    inference(resolution,[],[f193,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.47    inference(forward_demodulation,[],[f69,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    sK4 = sK5),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.47    inference(subsumption_resolution,[],[f192,f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.47    inference(subsumption_resolution,[],[f159,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK3)) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f158,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    v2_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK3)) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f157,f59])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK3)) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK3)) | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.21/0.47    inference(resolution,[],[f153,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.47    inference(resolution,[],[f152,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.47    inference(forward_demodulation,[],[f67,f68])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f47])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f151,f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f111,f57])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f110,f59])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f109,f63])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.47    inference(resolution,[],[f80,f65])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.21/0.47    inference(resolution,[],[f150,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f149,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3))),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f65])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f58])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f59])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | u1_struct_0(sK3) = k1_tops_1(sK1,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1)),
% 0.21/0.47    inference(resolution,[],[f128,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_tsep_1(sK3,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_tsep_1(X0,X1) | ~l1_pre_topc(X1) | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.48    inference(condensation,[],[f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = k1_tops_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X1) = k1_tops_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(condensation,[],[f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X1) | ~v1_tsep_1(X0,X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~v1_tsep_1(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.21/0.48    inference(resolution,[],[f123,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(u1_struct_0(X0),X1) | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(u1_struct_0(X0),X1) | u1_struct_0(X0) = k1_tops_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.48    inference(resolution,[],[f121,f73])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) = X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X0) = X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~m1_pre_topc(X3,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.48    inference(resolution,[],[f81,f73])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f57])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f58])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f59])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~r2_hidden(X0,k1_tops_1(sK1,u1_struct_0(sK3)))) )),
% 0.21/0.48    inference(resolution,[],[f119,f65])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_connsp_2(u1_struct_0(X2),X1,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~r2_hidden(X0,k1_tops_1(X1,u1_struct_0(X2)))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tops_1(X1,u1_struct_0(X2))) | m1_connsp_2(u1_struct_0(X2),X1,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.48    inference(resolution,[],[f76,f73])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.48    inference(subsumption_resolution,[],[f191,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.48    inference(resolution,[],[f190,f153])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_connsp_2(X0,sK1,sK4) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.21/0.48    inference(forward_demodulation,[],[f70,f68])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X0,sK1,sK4) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)) )),
% 0.21/0.48    inference(resolution,[],[f188,f103])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X0,sK1,X1) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f63])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X0,sK1,X1) | v2_struct_0(sK3) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.21/0.48    inference(resolution,[],[f186,f65])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,sK1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X0,sK1,X1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f183,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f57])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f58])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f180,f59])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f178,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_connsp_2(X4,X2,X3) | ~r1_tarski(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X0,X2) | v2_struct_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3) | r1_tmap_1(X2,X1,sK2,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f177,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f80])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f206,f54])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f55])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f204,f56])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f57])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f58])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f59])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f60])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f61])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f62])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f197,f63])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f65])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f195,f103])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    v1_xboole_0(u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f193,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f80])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6764)------------------------------
% 0.21/0.48  % (6764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6764)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6764)Memory used [KB]: 6396
% 0.21/0.48  % (6764)Time elapsed: 0.068 s
% 0.21/0.48  % (6764)------------------------------
% 0.21/0.48  % (6764)------------------------------
% 0.21/0.48  % (6741)Success in time 0.126 s
%------------------------------------------------------------------------------
