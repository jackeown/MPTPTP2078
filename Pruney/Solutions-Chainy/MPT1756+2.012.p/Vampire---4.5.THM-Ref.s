%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 (1286 expanded)
%              Number of leaves         :   15 ( 643 expanded)
%              Depth                    :   26
%              Number of atoms          :  870 (28178 expanded)
%              Number of equality atoms :   31 (1658 expanded)
%              Maximal formula depth    :   27 (  10 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(subsumption_resolution,[],[f258,f246])).

fof(f246,plain,(
    ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(unit_resulting_resolution,[],[f112,f110,f245])).

fof(f245,plain,(
    ! [X1] :
      ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ m1_connsp_2(X1,sK1,sK5)
      | ~ r1_tarski(X1,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f244,f71])).

fof(f71,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(backward_demodulation,[],[f55,f53])).

fof(f53,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f28,f27,f26,f25,f24,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f28,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f55,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f244,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f243,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f243,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | v2_struct_0(sK3)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(subsumption_resolution,[],[f241,f46])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f241,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ m1_connsp_2(X1,sK1,sK5)
      | ~ m1_pre_topc(sK3,sK1)
      | v2_struct_0(sK3)
      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(resolution,[],[f235,f72])).

% (3733)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f49,f53])).

fof(f49,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X1))
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ m1_connsp_2(X0,sK1,sK5)
      | ~ m1_pre_topc(X1,sK1)
      | v2_struct_0(X1)
      | ~ r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK5) ) ),
    inference(resolution,[],[f234,f48])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f233,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
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
    inference(subsumption_resolution,[],[f227,f43])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ r1_tarski(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_pre_topc(X2,sK1)
      | v2_struct_0(X2)
      | ~ r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | r1_tmap_1(sK1,sK0,sK2,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f107,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
      | ~ m1_connsp_2(X9,X7,X8)
      | ~ r1_tarski(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_pre_topc(X5,X7)
      | v2_struct_0(X5)
      | ~ r1_tmap_1(X5,X6,k2_tmap_1(X7,X6,sK2,X5),X8)
      | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(X6))
      | r1_tmap_1(X7,X6,sK2,X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f104,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f104,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_tmap_1(X5,X6,k2_tmap_1(X7,X6,sK2,X5),X8)
      | ~ m1_connsp_2(X9,X7,X8)
      | ~ r1_tarski(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_pre_topc(X5,X7)
      | v2_struct_0(X5)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
      | ~ v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(X6))
      | r1_tmap_1(X7,X6,sK2,X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f42,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
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
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,(
    m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5) ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f51,f50,f48,f47,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_connsp_2(sK8(X0,X1,X4),X0,X4)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK7(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK7(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK8(X0,X1,X4),X1)
                    & m1_connsp_2(sK8(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f33,f32])).

fof(f32,plain,(
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
            | ~ m1_connsp_2(X3,X0,sK7(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK8(X0,X1,X4),X1)
        & m1_connsp_2(sK8(X0,X1,X4),X0,X4)
        & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,(
    r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f52,f111,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f111,plain,(
    r1_tarski(sK8(sK1,sK4,sK5),sK4) ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f51,f50,f48,f47,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK8(X0,X1,X4),X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f258,plain,(
    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(unit_resulting_resolution,[],[f36,f37,f38,f39,f40,f41,f45,f42,f46,f72,f48,f43,f44,f248,f67])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f248,plain,(
    r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(global_subsumption,[],[f70,f246])).

fof(f70,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(backward_demodulation,[],[f54,f53])).

fof(f54,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6)
    | r1_tmap_1(sK1,sK0,sK2,sK5) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (3738)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (3746)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (3746)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (3734)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (3739)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (3748)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % (3742)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (3735)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f258,f246])).
% 0.20/0.48  fof(f246,plain,(
% 0.20/0.48    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f112,f110,f245])).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tarski(X1,u1_struct_0(sK3))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f244,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    sK5 = sK6),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    (((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f28,f27,f26,f25,f24,f23,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | ~r1_tmap_1(X1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X6) | r1_tmap_1(X1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | ~r1_tmap_1(sK1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | r1_tmap_1(sK1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | ~r1_tmap_1(sK1,sK0,X2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,X2,X3),X6) | r1_tmap_1(sK1,sK0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(X3,sK0,k2_tmap_1(sK1,sK0,sK2,X3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(sK3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X5] : (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,X5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,X5)) & X5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(X5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK1))) => (? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ? [X6] : ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),X6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = X6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(X6,u1_struct_0(sK3))) => ((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)) & sK5 = sK6 & r1_tarski(sK4,u1_struct_0(sK3)) & r2_hidden(sK5,sK4) & v3_pre_topc(sK4,sK1) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5))) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r1_tmap_1(X1,X0,X2,X5) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | ~r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,sK5) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f243,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,sK5) | v2_struct_0(sK3) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f241,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    m1_pre_topc(sK3,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK3)) | ~m1_connsp_2(X1,sK1,sK5) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.20/0.48    inference(resolution,[],[f235,f72])).
% 0.20/0.48  % (3733)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.48    inference(forward_demodulation,[],[f49,f53])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tarski(X0,u1_struct_0(X1)) | ~m1_connsp_2(X0,sK1,sK5) | ~m1_pre_topc(X1,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X1,sK0,k2_tmap_1(sK1,sK0,sK2,X1),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)) )),
% 0.20/0.48    inference(resolution,[],[f234,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_connsp_2(X0,sK1,X1) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f233,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f232,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f231,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f230,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f229,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v2_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f228,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    l1_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f227,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK1,X1) | ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~r1_tmap_1(X2,sK0,k2_tmap_1(sK1,sK0,sK2,X2),X1) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | r1_tmap_1(sK1,sK0,sK2,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f107,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6)))) | ~m1_connsp_2(X9,X7,X8) | ~r1_tarski(X9,u1_struct_0(X5)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_pre_topc(X5,X7) | v2_struct_0(X5) | ~r1_tmap_1(X5,X6,k2_tmap_1(X7,X6,sK2,X5),X8) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(X6)) | r1_tmap_1(X7,X6,sK2,X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f104,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ( ! [X6,X8,X7,X5,X9] : (~r1_tmap_1(X5,X6,k2_tmap_1(X7,X6,sK2,X5),X8) | ~m1_connsp_2(X9,X7,X8) | ~r1_tarski(X9,u1_struct_0(X5)) | ~m1_subset_1(X8,u1_struct_0(X5)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7))) | ~m1_pre_topc(X5,X7) | v2_struct_0(X5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6)))) | ~v1_funct_2(sK2,u1_struct_0(X7),u1_struct_0(X6)) | r1_tmap_1(X7,X6,sK2,X8) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.20/0.48    inference(resolution,[],[f42,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X1,X0,X2,X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    m1_connsp_2(sK8(sK1,sK4,sK5),sK1,sK5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f51,f50,f48,f47,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_connsp_2(sK8(X0,X1,X4),X0,X4) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK7(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK8(X0,X1,X4),X1) & m1_connsp_2(sK8(X0,X1,X4),X0,X4) & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f33,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK7(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK8(X0,X1,X4),X1) & m1_connsp_2(sK8(X0,X1,X4),X0,X4) & m1_subset_1(sK8(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(rectify,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    v3_pre_topc(sK4,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    r2_hidden(sK5,sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    r1_tarski(sK8(sK1,sK4,sK5),u1_struct_0(sK3))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f52,f111,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    r1_tarski(sK8(sK1,sK4,sK5),sK4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f39,f40,f41,f51,f50,f48,f47,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK8(X0,X1,X4),X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f258,plain,(
% 0.20/0.48    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f36,f37,f38,f39,f40,f41,f45,f42,f46,f72,f48,f43,f44,f248,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.48    inference(global_subsumption,[],[f70,f246])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.48    inference(backward_demodulation,[],[f54,f53])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK6) | r1_tmap_1(sK1,sK0,sK2,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (3746)------------------------------
% 0.20/0.48  % (3746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3746)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (3746)Memory used [KB]: 6524
% 0.20/0.48  % (3746)Time elapsed: 0.069 s
% 0.20/0.48  % (3746)------------------------------
% 0.20/0.48  % (3746)------------------------------
% 0.20/0.48  % (3730)Success in time 0.133 s
%------------------------------------------------------------------------------
