%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 (1105 expanded)
%              Number of leaves         :   17 ( 584 expanded)
%              Depth                    :   14
%              Number of atoms          :  799 (26927 expanded)
%              Number of equality atoms :   34 (1448 expanded)
%              Maximal formula depth    :   32 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f181,f252])).

fof(f252,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f185,f60])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f33,f41,f40,f39,f38,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
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
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
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
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK0,X4,X6) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,sK1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK0,X4,X6) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(X2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,sK1)
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK0,X4,X6) )
                          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,sK1)
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK0,X4,X6) )
                        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK1)
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,sK1)
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK0,X4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,sK1)
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK0,sK4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,sK1)
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK0,sK4,X6) )
                & X6 = X7
                & r1_tarski(X5,u1_struct_0(sK2))
                & r2_hidden(X6,X5)
                & v3_pre_topc(X5,sK1)
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK0,sK4,X6) )
              & X6 = X7
              & r1_tarski(sK5,u1_struct_0(sK2))
              & r2_hidden(X6,sK5)
              & v3_pre_topc(sK5,sK1)
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK0,sK4,X6) )
            & X6 = X7
            & r1_tarski(sK5,u1_struct_0(sK2))
            & r2_hidden(X6,sK5)
            & v3_pre_topc(sK5,sK1)
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK0,sK4,sK6) )
          & sK6 = X7
          & r1_tarski(sK5,u1_struct_0(sK2))
          & r2_hidden(sK6,sK5)
          & v3_pre_topc(sK5,sK1)
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK0,sK4,sK6) )
        & sK6 = X7
        & r1_tarski(sK5,u1_struct_0(sK2))
        & r2_hidden(sK6,sK5)
        & v3_pre_topc(sK5,sK1)
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
      & sK6 = sK7
      & r1_tarski(sK5,u1_struct_0(sK2))
      & r2_hidden(sK6,sK5)
      & v3_pre_topc(sK5,sK1)
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f32])).

% (24010)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
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

fof(f185,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f52,f53,f48,f49,f50,f54,f56,f58,f57,f161,f66,f61,f67,f118,f63,f91,f97,f59,f100,f165])).

fof(f165,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f89,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f89,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X7)
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
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tmap_1(X3,X1,X4,X6)
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
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f100,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f59,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f64,f68])).

fof(f68,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unit_resulting_resolution,[],[f110,f61,f106,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f106,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f67,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f53,f57,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f67,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f161,plain,(
    v3_pre_topc(sK5,sK3) ),
    inference(unit_resulting_resolution,[],[f53,f57,f65,f118,f153])).

fof(f153,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f90,f81])).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f65,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f181,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f166,f118])).

fof(f166,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f53,f57,f65,f160,f153])).

fof(f160,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f51,f52,f53,f48,f49,f50,f54,f56,f58,f57,f66,f61,f67,f63,f91,f103,f59,f101,f60,f118,f156])).

fof(f156,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
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
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f88,f83])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f103,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f93,f101])).

fof(f93,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f70,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f92,f99,f95])).

fof(f92,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(forward_demodulation,[],[f69,f68])).

fof(f69,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (23991)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.46  % (23991)Refutation not found, incomplete strategy% (23991)------------------------------
% 0.22/0.46  % (23991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (24008)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.47  % (23999)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.47  % (23991)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23991)Memory used [KB]: 10746
% 0.22/0.47  % (23991)Time elapsed: 0.057 s
% 0.22/0.47  % (23991)------------------------------
% 0.22/0.47  % (23991)------------------------------
% 0.22/0.50  % (24014)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (24006)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (23990)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (24003)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (23994)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (23997)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (23996)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (24002)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (24007)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (23992)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (24005)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (23990)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (23993)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (24013)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (24015)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (23998)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (23997)Refutation not found, incomplete strategy% (23997)------------------------------
% 0.22/0.53  % (23997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24000)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (23995)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f102,f181,f252])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ~spl8_1 | spl8_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f251])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    $false | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f185,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f33,f41,f40,f39,f38,f37,f36,f35,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  % (24010)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tmap_1)).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | (~spl8_1 | spl8_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f51,f52,f53,f48,f49,f50,f54,f56,f58,f57,f161,f66,f61,f67,f118,f63,f91,f97,f59,f100,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    r1_tmap_1(sK3,sK0,sK4,sK6) | ~spl8_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f64,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    sK6 = sK7),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    m1_subset_1(sK7,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f110,f61,f106,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f67,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    l1_pre_topc(sK3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f57,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    r1_tarski(sK5,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    r2_hidden(sK6,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    v3_pre_topc(sK5,sK3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f57,f65,f118,f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f81])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    v3_pre_topc(sK5,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    m1_pre_topc(sK3,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~v2_struct_0(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~v2_struct_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v2_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl8_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f180])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    $false | ~spl8_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f118])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f57,f65,f160,f153])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~v3_pre_topc(sK5,sK3) | ~spl8_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f51,f52,f53,f48,f49,f50,f54,f56,f58,f57,f66,f61,f67,f63,f91,f103,f59,f101,f60,f118,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f88,f83])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl8_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ~r1_tmap_1(sK3,sK0,sK4,sK6) | ~spl8_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f93,f101])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.22/0.53    inference(forward_demodulation,[],[f70,f68])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl8_1 | spl8_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f92,f99,f95])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.22/0.53    inference(forward_demodulation,[],[f69,f68])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (23990)------------------------------
% 0.22/0.53  % (23990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23990)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (23990)Memory used [KB]: 10874
% 0.22/0.53  % (23990)Time elapsed: 0.105 s
% 0.22/0.53  % (23990)------------------------------
% 0.22/0.53  % (23990)------------------------------
% 0.22/0.53  % (23986)Success in time 0.169 s
%------------------------------------------------------------------------------
