%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 728 expanded)
%              Number of leaves         :   17 ( 353 expanded)
%              Depth                    :   30
%              Number of atoms          : 1074 (15303 expanded)
%              Number of equality atoms :   37 ( 901 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f143,f160])).

% (6473)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f160,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f158,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
      | r1_tmap_1(sK3,sK2,sK4,sK7) )
    & sK7 = sK8
    & r1_tarski(sK6,u1_struct_0(sK5))
    & r2_hidden(sK7,sK6)
    & v3_pre_topc(sK6,sK3)
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f26,f25,f24,f23,f22,f21,f20])).

fof(f20,plain,
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
                              ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | ~ r1_tmap_1(X1,sK2,X2,X5) )
                              & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                                | r1_tmap_1(X1,sK2,X2,X5) )
                              & X5 = X6
                              & r1_tarski(X4,u1_struct_0(X3))
                              & r2_hidden(X5,X4)
                              & v3_pre_topc(X4,X1)
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                              | ~ r1_tmap_1(X1,sK2,X2,X5) )
                            & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6)
                              | r1_tmap_1(X1,sK2,X2,X5) )
                            & X5 = X6
                            & r1_tarski(X4,u1_struct_0(X3))
                            & r2_hidden(X5,X4)
                            & v3_pre_topc(X4,X1)
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6)
                            | ~ r1_tmap_1(sK3,sK2,X2,X5) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6)
                            | r1_tmap_1(sK3,sK2,X2,X5) )
                          & X5 = X6
                          & r1_tarski(X4,u1_struct_0(X3))
                          & r2_hidden(X5,X4)
                          & v3_pre_topc(X4,sK3)
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(sK3)) )
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6)
                          | ~ r1_tmap_1(sK3,sK2,X2,X5) )
                        & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6)
                          | r1_tmap_1(sK3,sK2,X2,X5) )
                        & X5 = X6
                        & r1_tarski(X4,u1_struct_0(X3))
                        & r2_hidden(X5,X4)
                        & v3_pre_topc(X4,sK3)
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(sK3)) )
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6)
                        | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
                      & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6)
                        | r1_tmap_1(sK3,sK2,sK4,X5) )
                      & X5 = X6
                      & r1_tarski(X4,u1_struct_0(X3))
                      & r2_hidden(X5,X4)
                      & v3_pre_topc(X4,sK3)
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(sK3)) )
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6)
                      | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
                    & ( r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6)
                      | r1_tmap_1(sK3,sK2,sK4,X5) )
                    & X5 = X6
                    & r1_tarski(X4,u1_struct_0(X3))
                    & r2_hidden(X5,X4)
                    & v3_pre_topc(X4,sK3)
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                    | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
                  & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                    | r1_tmap_1(sK3,sK2,sK4,X5) )
                  & X5 = X6
                  & r1_tarski(X4,u1_struct_0(sK5))
                  & r2_hidden(X5,X4)
                  & v3_pre_topc(X4,sK3)
                  & m1_subset_1(X6,u1_struct_0(sK5)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                  | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
                & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                  | r1_tmap_1(sK3,sK2,sK4,X5) )
                & X5 = X6
                & r1_tarski(X4,u1_struct_0(sK5))
                & r2_hidden(X5,X4)
                & v3_pre_topc(X4,sK3)
                & m1_subset_1(X6,u1_struct_0(sK5)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
              & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
                | r1_tmap_1(sK3,sK2,sK4,X5) )
              & X5 = X6
              & r1_tarski(sK6,u1_struct_0(sK5))
              & r2_hidden(X5,sK6)
              & v3_pre_topc(sK6,sK3)
              & m1_subset_1(X6,u1_struct_0(sK5)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
              | ~ r1_tmap_1(sK3,sK2,sK4,X5) )
            & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
              | r1_tmap_1(sK3,sK2,sK4,X5) )
            & X5 = X6
            & r1_tarski(sK6,u1_struct_0(sK5))
            & r2_hidden(X5,sK6)
            & v3_pre_topc(sK6,sK3)
            & m1_subset_1(X6,u1_struct_0(sK5)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
            | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
          & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
            | r1_tmap_1(sK3,sK2,sK4,sK7) )
          & sK7 = X6
          & r1_tarski(sK6,u1_struct_0(sK5))
          & r2_hidden(sK7,sK6)
          & v3_pre_topc(sK6,sK3)
          & m1_subset_1(X6,u1_struct_0(sK5)) )
      & m1_subset_1(sK7,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

% (6489)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f26,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
          | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
        & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6)
          | r1_tmap_1(sK3,sK2,sK4,sK7) )
        & sK7 = X6
        & r1_tarski(sK6,u1_struct_0(sK5))
        & r2_hidden(sK7,sK6)
        & v3_pre_topc(sK6,sK3)
        & m1_subset_1(X6,u1_struct_0(sK5)) )
   => ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
        | ~ r1_tmap_1(sK3,sK2,sK4,sK7) )
      & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
        | r1_tmap_1(sK3,sK2,sK4,sK7) )
      & sK7 = sK8
      & r1_tarski(sK6,u1_struct_0(sK5))
      & r2_hidden(sK7,sK6)
      & v3_pre_topc(sK6,sK3)
      & m1_subset_1(sK8,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f158,plain,
    ( v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f157,f38])).

fof(f38,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f157,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f156,f39])).

fof(f39,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f155,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f155,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f154,f41])).

fof(f41,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f154,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f153,f42])).

fof(f42,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f153,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f152,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f151,f44])).

fof(f44,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f150,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f150,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f149,plain,
    ( v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f148,f47])).

% (6496)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f47,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f147,f49])).

fof(f49,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f147,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f146,f86])).

fof(f86,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f50,f54])).

fof(f54,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f145,f78])).

fof(f78,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl10_1
  <=> r1_tmap_1(sK3,sK2,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f145,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl10_2 ),
    inference(resolution,[],[f144,f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f144,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | spl10_2 ),
    inference(forward_demodulation,[],[f83,f54])).

fof(f83,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl10_2
  <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f143,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f52,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( ~ r2_hidden(sK7,sK6)
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f140,f49])).

fof(f140,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | ~ r2_hidden(sK7,sK6)
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f139,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_connsp_2(sK6,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,sK6) ) ),
    inference(subsumption_resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_connsp_2(sK6,sK3,X0)
      | ~ r1_tarski(sK6,sK6)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(resolution,[],[f109,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,sK3)
      | ~ r1_tarski(sK6,X1)
      | ~ r2_hidden(X0,sK6) ) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,(
    v3_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK6)
      | ~ r1_tarski(sK6,X1)
      | ~ v3_pre_topc(sK6,sK3)
      | sP0(X0,X1,sK3) ) ),
    inference(resolution,[],[f63,f48])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,X1)
      | ~ v3_pre_topc(X3,X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( r2_hidden(X0,sK9(X0,X1,X2))
          & r1_tarski(sK9(X0,X1,X2),X1)
          & v3_pre_topc(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X0,sK9(X0,X1,X2))
        & r1_tarski(sK9(X0,X1,X2),X1)
        & v3_pre_topc(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f109,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK6,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | m1_connsp_2(sK6,sK3,X0) ) ),
    inference(resolution,[],[f108,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_connsp_2(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ m1_connsp_2(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( ( m1_connsp_2(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ m1_connsp_2(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( m1_connsp_2(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f108,plain,(
    ! [X0] :
      ( sP1(sK3,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,(
    ! [X0] :
      ( sP1(sK3,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,(
    ! [X0] :
      ( sP1(sK3,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,(
    ! [X0] :
      ( sP1(sK3,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f64,f48])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f139,plain,
    ( ~ m1_connsp_2(sK6,sK3,sK7)
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f137,f53])).

fof(f53,plain,(
    r1_tarski(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,
    ( ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ m1_connsp_2(sK6,sK3,sK7)
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f136,f48])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_connsp_2(X0,sK3,sK7) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f135,f37])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f131,f41])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f130,f42])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f129,f43])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f124,f49])).

% (6491)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(sK7,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f123,f86])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(sK7,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f120,f79])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f120,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK2,sK4,sK7)
        | ~ m1_connsp_2(X0,sK3,sK7)
        | ~ r1_tarski(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_subset_1(sK7,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl10_2 ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f82,f54])).

fof(f82,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6)
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
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f85,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f55,f81,f77])).

fof(f55,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f56,f81,f77])).

fof(f56,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK7) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (6474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (6474)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (6480)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f84,f85,f143,f160])).
% 0.22/0.51  % (6473)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ~spl10_1 | spl10_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f159])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    $false | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    (((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f26,f25,f24,f23,f22,f21,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | ~r1_tmap_1(X1,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X6) | r1_tmap_1(X1,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6) | ~r1_tmap_1(sK3,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6) | r1_tmap_1(sK3,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6) | ~r1_tmap_1(sK3,sK2,X2,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,X2,X3),X6) | r1_tmap_1(sK3,sK2,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(X3,sK2,k2_tmap_1(sK3,sK2,sK4,X3),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK5)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X5] : (? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,X5)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,X5)) & X5 = X6 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(X5,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = X6 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK3)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (6489)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X6] : ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X6) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = X6 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(X6,u1_struct_0(sK5))) => ((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)) & sK7 = sK8 & r1_tarski(sK6,u1_struct_0(sK5)) & r2_hidden(sK7,sK6) & v3_pre_topc(sK6,sK3) & m1_subset_1(sK8,u1_struct_0(sK5)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v2_pre_topc(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f155,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    v2_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f152,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f151,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f149,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~v2_struct_0(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f47])).
% 0.22/0.51  % (6496)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    m1_pre_topc(sK5,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    m1_subset_1(sK7,u1_struct_0(sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    m1_subset_1(sK7,u1_struct_0(sK5))),
% 0.22/0.51    inference(forward_demodulation,[],[f50,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    sK7 = sK8),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    m1_subset_1(sK8,u1_struct_0(sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl10_1 | spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    r1_tmap_1(sK3,sK2,sK4,sK7) | ~spl10_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl10_1 <=> r1_tmap_1(sK3,sK2,sK4,sK7)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK2,sK4,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl10_2),
% 0.22/0.51    inference(resolution,[],[f144,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | spl10_2),
% 0.22/0.51    inference(forward_demodulation,[],[f83,f54])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | spl10_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl10_2 <=> r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl10_1 | ~spl10_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    $false | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    r2_hidden(sK7,sK6)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~r2_hidden(sK7,sK6) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f49])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~r2_hidden(sK7,sK6) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(resolution,[],[f139,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X0] : (m1_connsp_2(sK6,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,sK6)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f111,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK6,sK3,X0) | ~r1_tarski(sK6,sK6) | ~r2_hidden(X0,sK6)) )),
% 0.22/0.51    inference(resolution,[],[f109,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP0(X0,X1,sK3) | ~r1_tarski(sK6,X1) | ~r2_hidden(X0,sK6)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f100,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    v3_pre_topc(sK6,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK6) | ~r1_tarski(sK6,X1) | ~v3_pre_topc(sK6,sK3) | sP0(X0,X1,sK3)) )),
% 0.22/0.51    inference(resolution,[],[f63,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK9(X0,X1,X2)) & r1_tarski(sK9(X0,X1,X2),X1) & v3_pre_topc(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f31,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK9(X0,X1,X2)) & r1_tarski(sK9(X0,X1,X2),X1) & v3_pre_topc(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0] : (~sP0(X0,sK6,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)) | m1_connsp_2(sK6,sK3,X0)) )),
% 0.22/0.51    inference(resolution,[],[f108,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | m1_connsp_2(X1,X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((m1_connsp_2(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~m1_connsp_2(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.51    inference(rectify,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X2,X1] : (((m1_connsp_2(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~m1_connsp_2(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X2,X1] : ((m1_connsp_2(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(sK3,sK6,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f40])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(sK3,sK6,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f41])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(sK3,sK6,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f42])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0] : (sP1(sK3,sK6,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(resolution,[],[f64,f48])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(definition_folding,[],[f10,f16,f15])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~m1_connsp_2(sK6,sK3,sK7) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r1_tarski(sK6,u1_struct_0(sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ~r1_tarski(sK6,u1_struct_0(sK5)) | ~m1_connsp_2(sK6,sK3,sK7) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(resolution,[],[f136,f48])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_connsp_2(X0,sK3,sK7)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f135,f37])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f38])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f39])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f40])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f41])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f130,f42])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f43])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f44])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f45])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f126,f46])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f47])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f49])).
% 0.22/0.51  % (6491)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f123,f86])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (spl10_1 | ~spl10_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f120,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ~r1_tmap_1(sK3,sK2,sK4,sK7) | spl10_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f77])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tmap_1(sK3,sK2,sK4,sK7) | ~m1_connsp_2(X0,sK3,sK7) | ~r1_tarski(X0,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_subset_1(sK7,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl10_2),
% 0.22/0.52    inference(resolution,[],[f72,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~spl10_2),
% 0.22/0.52    inference(forward_demodulation,[],[f82,f54])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~spl10_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl10_1 | spl10_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f55,f81,f77])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | r1_tmap_1(sK3,sK2,sK4,sK7)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~spl10_1 | ~spl10_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f56,f81,f77])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK8) | ~r1_tmap_1(sK3,sK2,sK4,sK7)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (6474)------------------------------
% 0.22/0.52  % (6474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6474)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (6474)Memory used [KB]: 6268
% 0.22/0.52  % (6474)Time elapsed: 0.073 s
% 0.22/0.52  % (6474)------------------------------
% 0.22/0.52  % (6474)------------------------------
% 0.22/0.52  % (6467)Success in time 0.155 s
%------------------------------------------------------------------------------
