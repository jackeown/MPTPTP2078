%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 (1459 expanded)
%              Number of leaves         :   22 ( 695 expanded)
%              Depth                    :   26
%              Number of atoms          : 1224 (29552 expanded)
%              Number of equality atoms :   28 (1715 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f289,f303,f455,f473])).

fof(f473,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f471,f445])).

fof(f445,plain,
    ( sP9(sK3,sK1,sK5)
    | ~ spl11_11 ),
    inference(resolution,[],[f444,f349])).

fof(f349,plain,
    ( r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f344,f52])).

% (30008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f52,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
      | r1_tmap_1(sK1,sK0,sK2,sK5) )
    & sK5 = sK6
    & r1_tarski(sK4,u1_struct_0(sK3))
    & r2_hidden(sK5,sK4)
    & v3_pre_topc(sK4,sK1)
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK3,sK1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f30,f29,f28,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | r1_tmap_1(X1,X0,X2,X5) )
                                & X5 = X6
                                & r1_tarski(X4,u1_struct_0(X3))
                                & r2_hidden(X5,X4)
                                & v3_pre_topc(X4,X1)
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X3,X1)
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
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK0,X2,X5) )
                              & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                                | r1_tmap_1(X1,sK0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                              | ~ r1_tmap_1(X1,sK0,X2,X5) )
                            & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6)
                              | r1_tmap_1(X1,sK0,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,X1)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(X3,X1)
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
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6)
                            | ~ r1_tmap_1(sK1,sK0,X2,X5) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6)
                            | r1_tmap_1(sK1,sK0,X2,X5) )
                          & X5 = X6
                          & r1_tarski(X4,u1_struct_0(X3))
                          & r2_hidden(X5,X4)
                          & v3_pre_topc(X4,sK1)
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6)
                          | ~ r1_tmap_1(sK1,sK0,X2,X5) )
                        & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6)
                          | r1_tmap_1(sK1,sK0,X2,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,sK1)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6)
                        | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
                      & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6)
                        | r1_tmap_1(sK1,sK0,sK2,X5) )
                      & X5 = X6
                      & r1_tarski(X4,u1_struct_0(X3))
                      & r2_hidden(X5,X4)
                      & v3_pre_topc(X4,sK1)
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6)
                      | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
                    & ( r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6)
                      | r1_tmap_1(sK1,sK0,sK2,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(X3))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,sK1)
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                    | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
                  & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                    | r1_tmap_1(sK1,sK0,sK2,X5) )
                  & X5 = X6
                  & r1_tarski(X4,u1_struct_0(sK3))
                  & r2_hidden(X5,X4)
                  & v3_pre_topc(X4,sK1)
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                  | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
                & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                  | r1_tmap_1(sK1,sK0,sK2,X5) )
                & X5 = X6
                & r1_tarski(X4,u1_struct_0(sK3))
                & r2_hidden(X5,X4)
                & v3_pre_topc(X4,sK1)
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
              & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
                | r1_tmap_1(sK1,sK0,sK2,X5) )
              & X5 = X6
              & r1_tarski(sK4,u1_struct_0(sK3))
              & r2_hidden(X5,sK4)
              & v3_pre_topc(sK4,sK1)
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
              | ~ r1_tmap_1(sK1,sK0,sK2,X5) )
            & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
              | r1_tmap_1(sK1,sK0,sK2,X5) )
            & X5 = X6
            & r1_tarski(sK4,u1_struct_0(sK3))
            & r2_hidden(X5,sK4)
            & v3_pre_topc(sK4,sK1)
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
            | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
          & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
            | r1_tmap_1(sK1,sK0,sK2,sK5) )
          & sK5 = X6
          & r1_tarski(sK4,u1_struct_0(sK3))
          & r2_hidden(sK5,sK4)
          & v3_pre_topc(sK4,sK1)
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
          | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
        & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6)
          | r1_tmap_1(sK1,sK0,sK2,sK5) )
        & sK5 = X6
        & r1_tarski(sK4,u1_struct_0(sK3))
        & r2_hidden(sK5,sK4)
        & v3_pre_topc(sK4,sK1)
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
        | ~ r1_tmap_1(sK1,sK0,sK2,sK5) )
      & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
        | r1_tmap_1(sK1,sK0,sK2,sK5) )
      & sK5 = sK6
      & r1_tarski(sK4,u1_struct_0(sK3))
      & r2_hidden(sK5,sK4)
      & v3_pre_topc(sK4,sK1)
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | ~ r1_tmap_1(X1,X0,X2,X5) )
                              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                | r1_tmap_1(X1,X0,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f8])).

% (30022)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f344,plain,
    ( r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl11_11 ),
    inference(resolution,[],[f277,f149])).

fof(f149,plain,(
    ! [X6] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X6)
      | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f148,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f148,plain,(
    ! [X6] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X6)
      | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f147,f44])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f147,plain,(
    ! [X6] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X6)
      | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,(
    ! [X6] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X6)
      | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3))
      | ~ m1_subset_1(X6,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_tarski(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK7(X0,X1,X2),X2)
                & v3_pre_topc(sK7(X0,X1,X2),X0)
                & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
                & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK7(X0,X1,X2),X2)
        & v3_pre_topc(sK7(X0,X1,X2),X0)
        & m1_connsp_2(sK7(X0,X1,X2),X0,X1)
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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

fof(f92,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f91,f45])).

fof(f91,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f50,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f277,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f275])).

% (30024)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f275,plain,
    ( spl11_11
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | sP9(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f443,f277])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
        | sP9(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f442,f52])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
        | sP9(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(resolution,[],[f320,f350])).

fof(f350,plain,
    ( m1_connsp_2(sK7(sK1,sK5,u1_struct_0(sK3)),sK1,sK5)
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f345,f52])).

fof(f345,plain,
    ( m1_connsp_2(sK7(sK1,sK5,u1_struct_0(sK3)),sK1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ spl11_11 ),
    inference(resolution,[],[f277,f143])).

fof(f143,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X4)
      | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f142,f43])).

fof(f142,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X4)
      | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f141,f44])).

fof(f141,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X4)
      | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f126,f45])).

fof(f126,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X4)
      | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_connsp_2(sK7(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f320,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_connsp_2(sK7(sK1,X16,u1_struct_0(sK3)),sK1,X18)
      | ~ m1_subset_1(X16,u1_struct_0(sK1))
      | ~ r1_tarski(sK7(sK1,X16,u1_struct_0(sK3)),u1_struct_0(X17))
      | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X16)
      | sP9(X17,sK1,X18) ) ),
    inference(resolution,[],[f140,f75])).

fof(f75,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP9(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f75_D])).

fof(f75_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP9(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f140,plain,(
    ! [X3] :
      ( m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f139,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X3)
      | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X3)
      | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f125,f45])).

fof(f125,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,X3)
      | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f471,plain,
    ( ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f470,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f470,plain,
    ( v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f469,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f469,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f468,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f468,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f467,f43])).

fof(f467,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f466,f44])).

fof(f466,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f465,f45])).

fof(f465,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f464,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f464,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f463,f47])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f463,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f462,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f462,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f461,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f461,plain,
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
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f460,f50])).

fof(f460,plain,
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
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f459,f52])).

fof(f459,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
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
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f458,f89])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f53,f57])).

fof(f57,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f458,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
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
    | ~ sP9(sK3,sK1,sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f457,f82])).

fof(f82,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK5)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl11_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f457,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
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
    | ~ sP9(sK3,sK1,sK5)
    | ~ spl11_2 ),
    inference(resolution,[],[f456,f76])).

fof(f76,plain,(
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
      | ~ sP9(X3,X1,X6) ) ),
    inference(general_splitting,[],[f73,f75_D])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f456,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f85,f57])).

fof(f85,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl11_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f455,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f453,f89])).

fof(f453,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f452,f215])).

fof(f215,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | spl11_2 ),
    inference(forward_demodulation,[],[f86,f57])).

fof(f86,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f452,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f451,f49])).

fof(f451,plain,
    ( v2_struct_0(sK3)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f450,f50])).

fof(f450,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl11_1
    | ~ spl11_11 ),
    inference(resolution,[],[f449,f265])).

% (30010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f265,plain,
    ( ! [X0] :
        ( ~ sP10(X0,sK1,sK5)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(X0)) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f264,f52])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5)
        | ~ sP10(X0,sK1,sK5) )
    | ~ spl11_1 ),
    inference(resolution,[],[f158,f81])).

fof(f81,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f157,f40])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f156,f41])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f155,f42])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tmap_1(sK1,sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f154,f43])).

fof(f154,plain,(
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
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f153,f44])).

fof(f153,plain,(
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
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f152,f45])).

fof(f152,plain,(
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
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f151,f46])).

fof(f151,plain,(
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
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f150,f47])).

% (30026)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f150,plain,(
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
      | v2_struct_0(sK0)
      | ~ sP10(X1,sK1,X0) ) ),
    inference(resolution,[],[f48,f78])).

fof(f78,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP10(X3,X1,X6) ) ),
    inference(general_splitting,[],[f74,f77_D])).

fof(f77,plain,(
    ! [X6,X4,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | sP10(X3,X1,X6) ) ),
    inference(cnf_transformation,[],[f77_D])).

fof(f77_D,plain,(
    ! [X6,X1,X3] :
      ( ! [X4] :
          ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
          | ~ r1_tarski(X4,u1_struct_0(X3))
          | ~ m1_connsp_2(X4,X1,X6) )
    <=> ~ sP10(X3,X1,X6) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
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
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
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
    inference(cnf_transformation,[],[f35])).

fof(f449,plain,
    ( sP10(sK3,sK1,sK5)
    | ~ spl11_11 ),
    inference(resolution,[],[f448,f349])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | sP10(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f447,f277])).

fof(f447,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
        | sP10(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f446,f52])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
        | ~ r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
        | sP10(X0,sK1,sK5) )
    | ~ spl11_11 ),
    inference(resolution,[],[f321,f350])).

fof(f321,plain,(
    ! [X21,X19,X20] :
      ( ~ m1_connsp_2(sK7(sK1,X19,u1_struct_0(sK3)),sK1,X21)
      | ~ m1_subset_1(X19,u1_struct_0(sK1))
      | ~ r1_tarski(sK7(sK1,X19,u1_struct_0(sK3)),u1_struct_0(X20))
      | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X19)
      | sP10(X20,sK1,X21) ) ),
    inference(resolution,[],[f140,f77])).

fof(f303,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f301,f56])).

fof(f56,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f301,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | spl11_13 ),
    inference(subsumption_resolution,[],[f300,f288])).

fof(f288,plain,
    ( ~ r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))
    | spl11_13 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl11_13
  <=> r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f300,plain,
    ( r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f297,f54])).

fof(f54,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f297,plain,
    ( ~ v3_pre_topc(sK4,sK1)
    | r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))
    | ~ r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f131,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | r1_tarski(X0,k1_tops_1(sK1,u1_struct_0(sK3)))
      | ~ r1_tarski(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK3))
      | ~ v3_pre_topc(X0,sK1)
      | r1_tarski(X0,k1_tops_1(sK1,u1_struct_0(sK3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f289,plain,
    ( ~ spl11_13
    | spl11_11 ),
    inference(avatar_split_clause,[],[f284,f275,f286])).

fof(f284,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f269,f52])).

fof(f269,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) ),
    inference(resolution,[],[f137,f93])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK5,X0)
      | ~ r1_tarski(sK4,X0) ) ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f55,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f137,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3)))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f136,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3)))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f135,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3)))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f124,f45])).

fof(f124,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3)))
      | m1_connsp_2(u1_struct_0(sK3),sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f92,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f88,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f58,f84,f80])).

fof(f58,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f59,f84,f80])).

fof(f59,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (29998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (30014)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (30006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (30002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (30006)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (29999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (30021)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (30013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (30003)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (30020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (30000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (30001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (30023)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (30005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f474,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f87,f88,f289,f303,f455,f473])).
% 0.20/0.54  fof(f473,plain,(
% 0.20/0.54    spl11_1 | ~spl11_2 | ~spl11_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f472])).
% 0.20/0.54  fof(f472,plain,(
% 0.20/0.54    $false | (spl11_1 | ~spl11_2 | ~spl11_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f471,f445])).
% 0.20/0.54  fof(f445,plain,(
% 0.20/0.54    sP9(sK3,sK1,sK5) | ~spl11_11),
% 0.20/0.54    inference(resolution,[],[f444,f349])).
% 0.20/0.54  fof(f349,plain,(
% 0.20/0.54    r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~spl11_11),
% 0.20/0.54    inference(subsumption_resolution,[],[f344,f52])).
% 0.20/0.54  % (30008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    (((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f30,f29,f28,f27,f26,f25,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | ~r1_tmap_1(sK1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | r1_tmap_1(sK1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | ~r1_tmap_1(sK1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | r1_tmap_1(sK1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) => (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  % (30022)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  fof(f8,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f7])).
% 0.20/0.54  fof(f7,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.20/0.54  fof(f344,plain,(
% 0.20/0.54    r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl11_11),
% 0.20/0.54    inference(resolution,[],[f277,f149])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X6] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X6) | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f148,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ~v2_struct_0(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    ( ! [X6] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X6) | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f147,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    v2_pre_topc(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ( ! [X6] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X6) | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f128,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    l1_pre_topc(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ( ! [X6] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X6) | r1_tarski(sK7(sK1,X6,u1_struct_0(sK3)),u1_struct_0(sK3)) | ~m1_subset_1(X6,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f92,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | r1_tarski(sK7(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f18,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK7(X0,X1,X2),X2) & v3_pre_topc(sK7(X0,X1,X2),X0) & m1_connsp_2(sK7(X0,X1,X2),X0,X1) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.54    inference(subsumption_resolution,[],[f91,f45])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.54    inference(resolution,[],[f50,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    m1_pre_topc(sK3,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f277,plain,(
% 0.20/0.54    m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~spl11_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f275])).
% 0.20/0.54  % (30024)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  fof(f275,plain,(
% 0.20/0.54    spl11_11 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.20/0.54  fof(f444,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | sP9(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.54    inference(subsumption_resolution,[],[f443,f277])).
% 0.20/0.54  fof(f443,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | sP9(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.54    inference(subsumption_resolution,[],[f442,f52])).
% 0.20/0.54  fof(f442,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | sP9(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.54    inference(resolution,[],[f320,f350])).
% 0.20/0.54  fof(f350,plain,(
% 0.20/0.54    m1_connsp_2(sK7(sK1,sK5,u1_struct_0(sK3)),sK1,sK5) | ~spl11_11),
% 0.20/0.54    inference(subsumption_resolution,[],[f345,f52])).
% 0.20/0.54  fof(f345,plain,(
% 0.20/0.54    m1_connsp_2(sK7(sK1,sK5,u1_struct_0(sK3)),sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~spl11_11),
% 0.20/0.54    inference(resolution,[],[f277,f143])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    ( ! [X4] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X4) | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f142,f43])).
% 0.20/0.54  fof(f142,plain,(
% 0.20/0.54    ( ! [X4] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X4) | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f141,f44])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    ( ! [X4] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X4) | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f126,f45])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X4] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X4) | m1_connsp_2(sK7(sK1,X4,u1_struct_0(sK3)),sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f92,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | m1_connsp_2(sK7(X0,X1,X2),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f320,plain,(
% 0.20/0.54    ( ! [X17,X18,X16] : (~m1_connsp_2(sK7(sK1,X16,u1_struct_0(sK3)),sK1,X18) | ~m1_subset_1(X16,u1_struct_0(sK1)) | ~r1_tarski(sK7(sK1,X16,u1_struct_0(sK3)),u1_struct_0(X17)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X16) | sP9(X17,sK1,X18)) )),
% 0.20/0.54    inference(resolution,[],[f140,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP9(X3,X1,X6)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f75_D])).
% 0.20/0.54  fof(f75_D,plain,(
% 0.20/0.54    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP9(X3,X1,X6)) )),
% 0.20/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    ( ! [X3] : (m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f139,f43])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    ( ! [X3] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X3) | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f138,f44])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    ( ! [X3] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X3) | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f125,f45])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    ( ! [X3] : (~m1_connsp_2(u1_struct_0(sK3),sK1,X3) | m1_subset_1(sK7(sK1,X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X3,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.54    inference(resolution,[],[f92,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f471,plain,(
% 0.20/0.54    ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f470,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ~v2_struct_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f470,plain,(
% 0.20/0.54    v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f469,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    v2_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f469,plain,(
% 0.20/0.54    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f468,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f468,plain,(
% 0.20/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f467,f43])).
% 0.20/0.54  fof(f467,plain,(
% 0.20/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f466,f44])).
% 0.20/0.54  fof(f466,plain,(
% 0.20/0.54    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f465,f45])).
% 0.20/0.54  fof(f465,plain,(
% 0.20/0.54    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f464,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    v1_funct_1(sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f464,plain,(
% 0.20/0.54    ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f463,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f462,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f461,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ~v2_struct_0(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f461,plain,(
% 0.20/0.54    v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f460,f50])).
% 0.20/0.54  fof(f460,plain,(
% 0.20/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f459,f52])).
% 0.20/0.54  fof(f459,plain,(
% 0.20/0.54    ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f458,f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.54    inference(forward_demodulation,[],[f53,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    sK5 = sK6),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f458,plain,(
% 0.20/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | (spl11_1 | ~spl11_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f457,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ~r1_tmap_1(sK1,sK0,sK2,sK5) | spl11_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    spl11_1 <=> r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.54  fof(f457,plain,(
% 0.20/0.54    r1_tmap_1(sK1,sK0,sK2,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP9(sK3,sK1,sK5) | ~spl11_2),
% 0.20/0.54    inference(resolution,[],[f456,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X6,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP9(X3,X1,X6)) )),
% 0.20/0.54    inference(general_splitting,[],[f73,f75_D])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~spl11_2),
% 0.20/0.54    inference(forward_demodulation,[],[f85,f57])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~spl11_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl11_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.20/0.54  fof(f455,plain,(
% 0.20/0.54    ~spl11_1 | spl11_2 | ~spl11_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f454])).
% 0.20/0.54  fof(f454,plain,(
% 0.20/0.54    $false | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f453,f89])).
% 0.20/0.54  fof(f453,plain,(
% 0.20/0.54    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl11_1 | spl11_2 | ~spl11_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f452,f215])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | spl11_2),
% 0.20/0.54    inference(forward_demodulation,[],[f86,f57])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | spl11_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f452,plain,(
% 0.20/0.54    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl11_1 | ~spl11_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f451,f49])).
% 0.20/0.54  fof(f451,plain,(
% 0.20/0.54    v2_struct_0(sK3) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl11_1 | ~spl11_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f450,f50])).
% 0.20/0.54  fof(f450,plain,(
% 0.20/0.54    ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl11_1 | ~spl11_11)),
% 0.20/0.54    inference(resolution,[],[f449,f265])).
% 0.20/0.54  % (30010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f265,plain,(
% 0.20/0.54    ( ! [X0] : (~sP10(X0,sK1,sK5) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0))) ) | ~spl11_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f264,f52])).
% 0.20/0.54  fof(f264,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X0) | r1_tmap_1(X0,sK0,k2_tmap_1(sK1,sK0,sK2,X0),sK5) | ~sP10(X0,sK1,sK5)) ) | ~spl11_1),
% 0.20/0.54    inference(resolution,[],[f158,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    r1_tmap_1(sK1,sK0,sK2,sK5) | ~spl11_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f80])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f157,f40])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f156,f41])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f155,f42])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f154,f43])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f153,f44])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f152,f45])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f151,f46])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f150,f47])).
% 0.20/0.54  % (30026)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tmap_1(sK1,sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),X0) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP10(X1,sK1,X0)) )),
% 0.20/0.55    inference(resolution,[],[f48,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X6,X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP10(X3,X1,X6)) )),
% 0.20/0.55    inference(general_splitting,[],[f74,f77_D])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X6,X4,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | sP10(X3,X1,X6)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f77_D])).
% 0.20/0.55  fof(f77_D,plain,(
% 0.20/0.55    ( ! [X6,X1,X3] : (( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6)) ) <=> ~sP10(X3,X1,X6)) )),
% 0.20/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f449,plain,(
% 0.20/0.55    sP10(sK3,sK1,sK5) | ~spl11_11),
% 0.20/0.55    inference(resolution,[],[f448,f349])).
% 0.20/0.55  fof(f448,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | sP10(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.55    inference(subsumption_resolution,[],[f447,f277])).
% 0.20/0.55  fof(f447,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | sP10(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.55    inference(subsumption_resolution,[],[f446,f52])).
% 0.20/0.55  fof(f446,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tarski(sK7(sK1,sK5,u1_struct_0(sK3)),u1_struct_0(X0)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | sP10(X0,sK1,sK5)) ) | ~spl11_11),
% 0.20/0.55    inference(resolution,[],[f321,f350])).
% 0.20/0.55  fof(f321,plain,(
% 0.20/0.55    ( ! [X21,X19,X20] : (~m1_connsp_2(sK7(sK1,X19,u1_struct_0(sK3)),sK1,X21) | ~m1_subset_1(X19,u1_struct_0(sK1)) | ~r1_tarski(sK7(sK1,X19,u1_struct_0(sK3)),u1_struct_0(X20)) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X19) | sP10(X20,sK1,X21)) )),
% 0.20/0.55    inference(resolution,[],[f140,f77])).
% 0.20/0.55  fof(f303,plain,(
% 0.20/0.55    spl11_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.55  fof(f302,plain,(
% 0.20/0.55    $false | spl11_13),
% 0.20/0.55    inference(subsumption_resolution,[],[f301,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f301,plain,(
% 0.20/0.55    ~r1_tarski(sK4,u1_struct_0(sK3)) | spl11_13),
% 0.20/0.55    inference(subsumption_resolution,[],[f300,f288])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    ~r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) | spl11_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f286])).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    spl11_13 <=> r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.20/0.55  fof(f300,plain,(
% 0.20/0.55    r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) | ~r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.55    inference(subsumption_resolution,[],[f297,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    v3_pre_topc(sK4,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f297,plain,(
% 0.20/0.55    ~v3_pre_topc(sK4,sK1) | r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3))) | ~r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.55    inference(resolution,[],[f131,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | r1_tarski(X0,k1_tops_1(sK1,u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK3))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f122,f45])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK3)) | ~v3_pre_topc(X0,sK1) | r1_tarski(X0,k1_tops_1(sK1,u1_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) )),
% 0.20/0.55    inference(resolution,[],[f92,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    ~spl11_13 | spl11_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f284,f275,f286])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f269,f52])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    m1_connsp_2(u1_struct_0(sK3),sK1,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | ~r1_tarski(sK4,k1_tops_1(sK1,u1_struct_0(sK3)))),
% 0.20/0.55    inference(resolution,[],[f137,f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(sK5,X0) | ~r1_tarski(sK4,X0)) )),
% 0.20/0.55    inference(resolution,[],[f55,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f37,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    r2_hidden(sK5,sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3))) | m1_connsp_2(u1_struct_0(sK3),sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f136,f43])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3))) | m1_connsp_2(u1_struct_0(sK3),sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f135,f44])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3))) | m1_connsp_2(u1_struct_0(sK3),sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f124,f45])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X2] : (~r2_hidden(X2,k1_tops_1(sK1,u1_struct_0(sK3))) | m1_connsp_2(u1_struct_0(sK3),sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.55    inference(resolution,[],[f92,f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    spl11_1 | spl11_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f58,f84,f80])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ~spl11_1 | ~spl11_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f59,f84,f80])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (30006)------------------------------
% 0.20/0.55  % (30006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30006)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (30006)Memory used [KB]: 11129
% 0.20/0.55  % (30006)Time elapsed: 0.130 s
% 0.20/0.55  % (30006)------------------------------
% 0.20/0.55  % (30006)------------------------------
% 0.20/0.55  % (30012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (30016)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (30018)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (29997)Success in time 0.188 s
%------------------------------------------------------------------------------
