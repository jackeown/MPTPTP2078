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
% DateTime   : Thu Dec  3 13:19:01 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 969 expanded)
%              Number of leaves         :   33 ( 487 expanded)
%              Depth                    :   25
%              Number of atoms          : 1008 (14529 expanded)
%              Number of equality atoms :   74 (1922 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14798)Refutation not found, incomplete strategy% (14798)------------------------------
% (14798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14798)Termination reason: Refutation not found, incomplete strategy

% (14798)Memory used [KB]: 10746
% (14798)Time elapsed: 0.143 s
% (14798)------------------------------
% (14798)------------------------------
% (14803)Refutation not found, incomplete strategy% (14803)------------------------------
% (14803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14803)Termination reason: Refutation not found, incomplete strategy

% (14803)Memory used [KB]: 6396
% (14803)Time elapsed: 0.153 s
% (14803)------------------------------
% (14803)------------------------------
% (14818)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f164,f183,f213,f257,f565,f567])).

fof(f567,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl9_13 ),
    inference(subsumption_resolution,[],[f256,f298])).

fof(f298,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f297,f123])).

fof(f123,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f120,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f56,f55,f54,f53,f52,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,
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

fof(f52,plain,
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

fof(f53,plain,
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

fof(f54,plain,
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

fof(f55,plain,
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

fof(f56,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f120,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f70,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f70,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f297,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f174,f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f168,f123])).

fof(f168,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f87,f76])).

fof(f76,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f256,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl9_13
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f565,plain,
    ( ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6
    | spl9_12 ),
    inference(subsumption_resolution,[],[f563,f252])).

fof(f252,plain,
    ( ~ sP7(sK3,sK2,sK5)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl9_12
  <=> sP7(sK3,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f563,plain,
    ( sP7(sK3,sK2,sK5)
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f559,f155])).

fof(f155,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_3
  <=> r2_hidden(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f559,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK2))
        | sP7(sK3,sK2,X0) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f545,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f545,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | sP7(sK3,X0,X1)
        | ~ r2_hidden(X1,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f544,f111])).

fof(f544,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0))
        | sP7(sK3,X0,X1)
        | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2))
        | ~ r2_hidden(X1,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f543,f528])).

fof(f528,plain,
    ( ! [X0] :
        ( m1_connsp_2(u1_struct_0(sK2),sK3,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f526,f351])).

fof(f351,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f208,f342])).

fof(f342,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(trivial_inequality_removal,[],[f341])).

fof(f341,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f182,f231])).

fof(f231,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f230,f131])).

fof(f131,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f128,f65])).

fof(f128,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f89])).

fof(f72,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f230,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f219,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f219,plain,
    ( v1_pre_topc(sK3)
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f214,f76])).

fof(f214,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl9_5 ),
    inference(resolution,[],[f178,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f178,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl9_5
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f182,plain,
    ( ! [X4,X5] :
        ( sK3 != g1_pre_topc(X4,X5)
        | u1_struct_0(sK2) = X4 )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl9_6
  <=> ! [X5,X4] :
        ( sK3 != g1_pre_topc(X4,X5)
        | u1_struct_0(sK2) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f208,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f207,f130])).

fof(f130,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f129,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f129,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f127,f65])).

fof(f127,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f72,f95])).

% (14813)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
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
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f207,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f206,f131])).

fof(f206,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(superposition,[],[f94,f135])).

fof(f135,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f133,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f133,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f94,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f526,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
        | m1_connsp_2(u1_struct_0(sK2),sK3,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f525,f111])).

fof(f525,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK2))
        | ~ v3_pre_topc(X1,sK3)
        | m1_connsp_2(X1,sK3,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f371,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f371,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | m1_connsp_2(X2,sK3,X3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f370,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f370,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | m1_connsp_2(X2,sK3,X3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f369,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f369,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | m1_connsp_2(X2,sK3,X3)
        | v2_struct_0(sK3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f368,f130])).

fof(f368,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | m1_connsp_2(X2,sK3,X3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f362,f131])).

fof(f362,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X3,X2)
        | ~ v3_pre_topc(X2,sK3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | m1_connsp_2(X2,sK3,X3)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f91,f342])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f543,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_connsp_2(X0,sK3,X2)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | sP7(sK3,X1,X2)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f363,f106])).

fof(f363,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X4,u1_struct_0(X5))
        | ~ m1_connsp_2(X4,sK3,X6)
        | sP7(sK3,X5,X6) )
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f112,f342])).

fof(f112,plain,(
    ! [X2,X7,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ m1_connsp_2(X5,X3,X7)
      | sP7(X3,X2,X7) ) ),
    inference(cnf_transformation,[],[f112_D])).

fof(f112_D,plain,(
    ! [X7,X2,X3] :
      ( ! [X5] :
          ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
          | ~ r1_tarski(X5,u1_struct_0(X2))
          | ~ m1_connsp_2(X5,X3,X7) )
    <=> ~ sP7(X3,X2,X7) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f257,plain,
    ( ~ spl9_12
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f248,f254,f250])).

fof(f248,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f247,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f247,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f246,f64])).

fof(f246,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f245,f65])).

fof(f245,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f244,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f244,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f243,f67])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f243,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f242,f68])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f241,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f241,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f240,f70])).

fof(f240,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f239,f71])).

fof(f239,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f238,f72])).

fof(f238,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f237,f73])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f237,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f236,f74])).

fof(f74,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f235,f75])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f235,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f234,f77])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f57])).

fof(f234,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f233,f146])).

fof(f146,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f78,f79])).

fof(f79,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f233,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(subsumption_resolution,[],[f232,f81])).

fof(f81,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f232,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ sP7(sK3,sK2,sK5) ),
    inference(resolution,[],[f209,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
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
      | v2_struct_0(X0)
      | ~ sP7(X3,X2,X7) ) ),
    inference(general_splitting,[],[f108,f112_D])).

fof(f108,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ m1_connsp_2(X5,X3,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ m1_connsp_2(X5,X3,X6)
      | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
                                  | ~ m1_connsp_2(X5,X3,X6)
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
                                        & m1_connsp_2(X5,X3,X6)
                                        & r1_tarski(X5,u1_struct_0(X2)) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

fof(f209,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(forward_demodulation,[],[f80,f79])).

fof(f80,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f213,plain,(
    spl9_5 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl9_5 ),
    inference(subsumption_resolution,[],[f210,f123])).

fof(f210,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_5 ),
    inference(resolution,[],[f179,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f179,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f177])).

fof(f183,plain,
    ( ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f171,f181,f177])).

fof(f171,plain,(
    ! [X4,X5] :
      ( sK3 != g1_pre_topc(X4,X5)
      | u1_struct_0(sK2) = X4
      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f100,f76])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f164,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f162,f69])).

fof(f162,plain,
    ( v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f161,f132])).

fof(f132,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f123,f83])).

fof(f161,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_4 ),
    inference(resolution,[],[f159,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f159,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_4
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f160,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f151,f157,f153])).

fof(f151,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(resolution,[],[f146,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (14810)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.16/0.53  % (14820)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.16/0.53  % (14800)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.16/0.54  % (14811)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.16/0.54  % (14812)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.16/0.54  % (14817)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.35/0.54  % (14801)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.35/0.54  % (14803)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.35/0.54  % (14802)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.35/0.54  % (14823)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.35/0.54  % (14807)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.35/0.55  % (14806)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.35/0.55  % (14809)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.35/0.55  % (14816)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.35/0.55  % (14805)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.35/0.55  % (14822)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.35/0.55  % (14815)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.35/0.55  % (14804)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.35/0.56  % (14819)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.35/0.56  % (14799)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.56  % (14814)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.35/0.56  % (14821)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.35/0.56  % (14798)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.35/0.56  % (14808)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.35/0.56  % (14799)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % SZS output start Proof for theBenchmark
% 1.35/0.57  % (14798)Refutation not found, incomplete strategy% (14798)------------------------------
% 1.35/0.57  % (14798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (14798)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (14798)Memory used [KB]: 10746
% 1.35/0.57  % (14798)Time elapsed: 0.143 s
% 1.35/0.57  % (14798)------------------------------
% 1.35/0.57  % (14798)------------------------------
% 1.35/0.57  % (14803)Refutation not found, incomplete strategy% (14803)------------------------------
% 1.35/0.57  % (14803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (14803)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (14803)Memory used [KB]: 6396
% 1.35/0.57  % (14803)Time elapsed: 0.153 s
% 1.35/0.57  % (14803)------------------------------
% 1.35/0.57  % (14803)------------------------------
% 1.35/0.57  % (14818)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.35/0.57  fof(f568,plain,(
% 1.35/0.57    $false),
% 1.35/0.57    inference(avatar_sat_refutation,[],[f160,f164,f183,f213,f257,f565,f567])).
% 1.35/0.57  fof(f567,plain,(
% 1.35/0.57    spl9_13),
% 1.35/0.57    inference(avatar_contradiction_clause,[],[f566])).
% 1.35/0.57  fof(f566,plain,(
% 1.35/0.57    $false | spl9_13),
% 1.35/0.57    inference(subsumption_resolution,[],[f256,f298])).
% 1.35/0.57  fof(f298,plain,(
% 1.35/0.57    m1_pre_topc(sK2,sK3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f297,f123])).
% 1.35/0.57  fof(f123,plain,(
% 1.35/0.57    l1_pre_topc(sK2)),
% 1.35/0.57    inference(subsumption_resolution,[],[f120,f65])).
% 1.35/0.57  fof(f65,plain,(
% 1.35/0.57    l1_pre_topc(sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f57,plain,(
% 1.35/0.57    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.35/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f56,f55,f54,f53,f52,f51,f50])).
% 1.35/0.57  fof(f50,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f51,plain,(
% 1.35/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f52,plain,(
% 1.35/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f53,plain,(
% 1.35/0.57    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f54,plain,(
% 1.35/0.57    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f55,plain,(
% 1.35/0.57    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f56,plain,(
% 1.35/0.57    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f23,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f22])).
% 1.35/0.57  fof(f22,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f21])).
% 1.35/0.57  fof(f21,negated_conjecture,(
% 1.35/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.35/0.57    inference(negated_conjecture,[],[f20])).
% 1.35/0.57  fof(f20,conjecture,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.35/0.57  fof(f120,plain,(
% 1.35/0.57    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.35/0.57    inference(resolution,[],[f70,f89])).
% 1.35/0.57  fof(f89,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f31])).
% 1.35/0.57  fof(f31,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f10])).
% 1.35/0.57  fof(f10,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.35/0.57  fof(f70,plain,(
% 1.35/0.57    m1_pre_topc(sK2,sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f297,plain,(
% 1.35/0.57    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.35/0.57    inference(duplicate_literal_removal,[],[f296])).
% 1.35/0.57  fof(f296,plain,(
% 1.35/0.57    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 1.35/0.57    inference(resolution,[],[f174,f84])).
% 1.35/0.57  fof(f84,plain,(
% 1.35/0.57    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f26])).
% 1.35/0.57  fof(f26,plain,(
% 1.35/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f17])).
% 1.35/0.57  fof(f17,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.35/0.57  fof(f174,plain,(
% 1.35/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(subsumption_resolution,[],[f168,f123])).
% 1.35/0.57  fof(f168,plain,(
% 1.35/0.57    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(superposition,[],[f87,f76])).
% 1.35/0.57  fof(f76,plain,(
% 1.35/0.57    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f87,plain,(
% 1.35/0.57    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f58])).
% 1.35/0.57  fof(f58,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(nnf_transformation,[],[f30])).
% 1.35/0.57  fof(f30,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f14])).
% 1.35/0.57  fof(f14,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.35/0.57  fof(f256,plain,(
% 1.35/0.57    ~m1_pre_topc(sK2,sK3) | spl9_13),
% 1.35/0.57    inference(avatar_component_clause,[],[f254])).
% 1.35/0.57  fof(f254,plain,(
% 1.35/0.57    spl9_13 <=> m1_pre_topc(sK2,sK3)),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.35/0.57  fof(f565,plain,(
% 1.35/0.57    ~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_12),
% 1.35/0.57    inference(avatar_contradiction_clause,[],[f564])).
% 1.35/0.57  fof(f564,plain,(
% 1.35/0.57    $false | (~spl9_3 | ~spl9_5 | ~spl9_6 | spl9_12)),
% 1.35/0.57    inference(subsumption_resolution,[],[f563,f252])).
% 1.35/0.57  fof(f252,plain,(
% 1.35/0.57    ~sP7(sK3,sK2,sK5) | spl9_12),
% 1.35/0.57    inference(avatar_component_clause,[],[f250])).
% 1.35/0.57  fof(f250,plain,(
% 1.35/0.57    spl9_12 <=> sP7(sK3,sK2,sK5)),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.35/0.57  fof(f563,plain,(
% 1.35/0.57    sP7(sK3,sK2,sK5) | (~spl9_3 | ~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(resolution,[],[f559,f155])).
% 1.35/0.57  fof(f155,plain,(
% 1.35/0.57    r2_hidden(sK5,u1_struct_0(sK2)) | ~spl9_3),
% 1.35/0.57    inference(avatar_component_clause,[],[f153])).
% 1.35/0.57  fof(f153,plain,(
% 1.35/0.57    spl9_3 <=> r2_hidden(sK5,u1_struct_0(sK2))),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.35/0.57  fof(f559,plain,(
% 1.35/0.57    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2)) | sP7(sK3,sK2,X0)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(resolution,[],[f545,f111])).
% 1.35/0.57  fof(f111,plain,(
% 1.35/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.35/0.57    inference(equality_resolution,[],[f102])).
% 1.35/0.57  fof(f102,plain,(
% 1.35/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.35/0.57    inference(cnf_transformation,[],[f61])).
% 1.35/0.57  fof(f61,plain,(
% 1.35/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.57    inference(flattening,[],[f60])).
% 1.35/0.57  fof(f60,plain,(
% 1.35/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.57    inference(nnf_transformation,[],[f1])).
% 1.35/0.57  fof(f1,axiom,(
% 1.35/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.57  fof(f545,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | sP7(sK3,X0,X1) | ~r2_hidden(X1,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(subsumption_resolution,[],[f544,f111])).
% 1.35/0.57  fof(f544,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) | sP7(sK3,X0,X1) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) | ~r2_hidden(X1,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(resolution,[],[f543,f528])).
% 1.35/0.57  fof(f528,plain,(
% 1.35/0.57    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK2),sK3,X0) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(subsumption_resolution,[],[f526,f351])).
% 1.35/0.57  fof(f351,plain,(
% 1.35/0.57    v3_pre_topc(u1_struct_0(sK2),sK3) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(backward_demodulation,[],[f208,f342])).
% 1.35/0.57  fof(f342,plain,(
% 1.35/0.57    u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(trivial_inequality_removal,[],[f341])).
% 1.35/0.57  fof(f341,plain,(
% 1.35/0.57    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(superposition,[],[f182,f231])).
% 1.35/0.57  fof(f231,plain,(
% 1.35/0.57    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~spl9_5),
% 1.35/0.57    inference(subsumption_resolution,[],[f230,f131])).
% 1.35/0.57  fof(f131,plain,(
% 1.35/0.57    l1_pre_topc(sK3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f128,f65])).
% 1.35/0.57  fof(f128,plain,(
% 1.35/0.57    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.35/0.57    inference(resolution,[],[f72,f89])).
% 1.35/0.57  fof(f72,plain,(
% 1.35/0.57    m1_pre_topc(sK3,sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f230,plain,(
% 1.35/0.57    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3) | ~spl9_5),
% 1.35/0.57    inference(resolution,[],[f219,f86])).
% 1.35/0.57  fof(f86,plain,(
% 1.35/0.57    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f29])).
% 1.35/0.57  fof(f29,plain,(
% 1.35/0.57    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(flattening,[],[f28])).
% 1.35/0.57  fof(f28,plain,(
% 1.35/0.57    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f5])).
% 1.35/0.57  fof(f5,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.35/0.57  fof(f219,plain,(
% 1.35/0.57    v1_pre_topc(sK3) | ~spl9_5),
% 1.35/0.57    inference(forward_demodulation,[],[f214,f76])).
% 1.35/0.57  fof(f214,plain,(
% 1.35/0.57    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl9_5),
% 1.35/0.57    inference(resolution,[],[f178,f98])).
% 1.35/0.57  fof(f98,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.35/0.57    inference(cnf_transformation,[],[f46])).
% 1.35/0.57  fof(f46,plain,(
% 1.35/0.57    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.57    inference(ennf_transformation,[],[f8])).
% 1.35/0.57  fof(f8,axiom,(
% 1.35/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.35/0.57  fof(f178,plain,(
% 1.35/0.57    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl9_5),
% 1.35/0.57    inference(avatar_component_clause,[],[f177])).
% 1.35/0.57  fof(f177,plain,(
% 1.35/0.57    spl9_5 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.35/0.57  fof(f182,plain,(
% 1.35/0.57    ( ! [X4,X5] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4) ) | ~spl9_6),
% 1.35/0.57    inference(avatar_component_clause,[],[f181])).
% 1.35/0.57  fof(f181,plain,(
% 1.35/0.57    spl9_6 <=> ! [X5,X4] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4)),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.35/0.57  fof(f208,plain,(
% 1.35/0.57    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f207,f130])).
% 1.35/0.57  fof(f130,plain,(
% 1.35/0.57    v2_pre_topc(sK3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f129,f64])).
% 1.35/0.57  fof(f64,plain,(
% 1.35/0.57    v2_pre_topc(sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f129,plain,(
% 1.35/0.57    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 1.35/0.57    inference(subsumption_resolution,[],[f127,f65])).
% 1.35/0.57  fof(f127,plain,(
% 1.35/0.57    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.35/0.57    inference(resolution,[],[f72,f95])).
% 1.35/0.57  % (14813)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.35/0.57  fof(f95,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f41])).
% 1.35/0.57  fof(f41,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.35/0.57    inference(flattening,[],[f40])).
% 1.35/0.57  fof(f40,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f6])).
% 1.35/0.57  fof(f6,axiom,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.35/0.57  fof(f207,plain,(
% 1.35/0.57    v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f206,f131])).
% 1.35/0.57  fof(f206,plain,(
% 1.35/0.57    v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.35/0.57    inference(superposition,[],[f94,f135])).
% 1.35/0.57  fof(f135,plain,(
% 1.35/0.57    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.35/0.57    inference(resolution,[],[f133,f82])).
% 1.35/0.57  fof(f82,plain,(
% 1.35/0.57    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f24])).
% 1.35/0.57  fof(f24,plain,(
% 1.35/0.57    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f7])).
% 1.35/0.57  fof(f7,axiom,(
% 1.35/0.57    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.35/0.57  fof(f133,plain,(
% 1.35/0.57    l1_struct_0(sK3)),
% 1.35/0.57    inference(resolution,[],[f131,f83])).
% 1.35/0.57  fof(f83,plain,(
% 1.35/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f25])).
% 1.35/0.57  fof(f25,plain,(
% 1.35/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f9])).
% 1.35/0.57  fof(f9,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.35/0.57  fof(f94,plain,(
% 1.35/0.57    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f39])).
% 1.35/0.57  fof(f39,plain,(
% 1.35/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.35/0.57    inference(flattening,[],[f38])).
% 1.35/0.57  fof(f38,plain,(
% 1.35/0.57    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f15])).
% 1.35/0.57  fof(f15,axiom,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.35/0.57  fof(f526,plain,(
% 1.35/0.57    ( ! [X0] : (~v3_pre_topc(u1_struct_0(sK2),sK3) | m1_connsp_2(u1_struct_0(sK2),sK3,X0) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(resolution,[],[f525,f111])).
% 1.35/0.57  fof(f525,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK2)) | ~v3_pre_topc(X1,sK3) | m1_connsp_2(X1,sK3,X0) | ~r2_hidden(X0,X1)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(resolution,[],[f371,f106])).
% 1.35/0.57  fof(f106,plain,(
% 1.35/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f62])).
% 1.35/0.57  fof(f62,plain,(
% 1.35/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.35/0.57    inference(nnf_transformation,[],[f3])).
% 1.35/0.57  fof(f3,axiom,(
% 1.35/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.35/0.57  fof(f371,plain,(
% 1.35/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | m1_connsp_2(X2,sK3,X3)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(subsumption_resolution,[],[f370,f107])).
% 1.35/0.57  fof(f107,plain,(
% 1.35/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f49])).
% 1.35/0.57  fof(f49,plain,(
% 1.35/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.35/0.57    inference(flattening,[],[f48])).
% 1.35/0.57  fof(f48,plain,(
% 1.35/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.35/0.57    inference(ennf_transformation,[],[f4])).
% 1.35/0.57  fof(f4,axiom,(
% 1.35/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.35/0.57  fof(f370,plain,(
% 1.35/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | m1_connsp_2(X2,sK3,X3)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(subsumption_resolution,[],[f369,f71])).
% 1.35/0.57  fof(f71,plain,(
% 1.35/0.57    ~v2_struct_0(sK3)),
% 1.35/0.57    inference(cnf_transformation,[],[f57])).
% 1.35/0.57  fof(f369,plain,(
% 1.35/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | m1_connsp_2(X2,sK3,X3) | v2_struct_0(sK3)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.57    inference(subsumption_resolution,[],[f368,f130])).
% 1.35/0.58  fof(f368,plain,(
% 1.35/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | m1_connsp_2(X2,sK3,X3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.58    inference(subsumption_resolution,[],[f362,f131])).
% 1.35/0.58  fof(f362,plain,(
% 1.35/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X3,X2) | ~v3_pre_topc(X2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK2)) | m1_connsp_2(X2,sK3,X3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.58    inference(superposition,[],[f91,f342])).
% 1.35/0.58  fof(f91,plain,(
% 1.35/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f35])).
% 1.35/0.58  fof(f35,plain,(
% 1.35/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.58    inference(flattening,[],[f34])).
% 1.35/0.58  fof(f34,plain,(
% 1.35/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.58    inference(ennf_transformation,[],[f16])).
% 1.35/0.58  fof(f16,axiom,(
% 1.35/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.35/0.58  fof(f543,plain,(
% 1.35/0.58    ( ! [X2,X0,X1] : (~m1_connsp_2(X0,sK3,X2) | ~r1_tarski(X0,u1_struct_0(X1)) | sP7(sK3,X1,X2) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.58    inference(resolution,[],[f363,f106])).
% 1.35/0.58  fof(f363,plain,(
% 1.35/0.58    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X4,u1_struct_0(X5)) | ~m1_connsp_2(X4,sK3,X6) | sP7(sK3,X5,X6)) ) | (~spl9_5 | ~spl9_6)),
% 1.35/0.58    inference(superposition,[],[f112,f342])).
% 1.35/0.58  fof(f112,plain,(
% 1.35/0.58    ( ! [X2,X7,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7) | sP7(X3,X2,X7)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f112_D])).
% 1.35/0.58  fof(f112_D,plain,(
% 1.35/0.58    ( ! [X7,X2,X3] : (( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_connsp_2(X5,X3,X7)) ) <=> ~sP7(X3,X2,X7)) )),
% 1.35/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.35/0.58  fof(f257,plain,(
% 1.35/0.58    ~spl9_12 | ~spl9_13),
% 1.35/0.58    inference(avatar_split_clause,[],[f248,f254,f250])).
% 1.35/0.58  fof(f248,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f247,f63])).
% 1.35/0.58  fof(f63,plain,(
% 1.35/0.58    ~v2_struct_0(sK0)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f247,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f246,f64])).
% 1.35/0.58  fof(f246,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f245,f65])).
% 1.35/0.58  fof(f245,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f244,f66])).
% 1.35/0.58  fof(f66,plain,(
% 1.35/0.58    ~v2_struct_0(sK1)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f244,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f243,f67])).
% 1.35/0.58  fof(f67,plain,(
% 1.35/0.58    v2_pre_topc(sK1)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f243,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f242,f68])).
% 1.35/0.58  fof(f68,plain,(
% 1.35/0.58    l1_pre_topc(sK1)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f242,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f241,f69])).
% 1.35/0.58  fof(f69,plain,(
% 1.35/0.58    ~v2_struct_0(sK2)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f241,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f240,f70])).
% 1.35/0.58  fof(f240,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f239,f71])).
% 1.35/0.58  fof(f239,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f238,f72])).
% 1.35/0.58  fof(f238,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f237,f73])).
% 1.35/0.58  fof(f73,plain,(
% 1.35/0.58    v1_funct_1(sK4)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f237,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f236,f74])).
% 1.35/0.58  fof(f74,plain,(
% 1.35/0.58    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f236,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f235,f75])).
% 1.35/0.58  fof(f75,plain,(
% 1.35/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f235,plain,(
% 1.35/0.58    ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f234,f77])).
% 1.35/0.58  fof(f77,plain,(
% 1.35/0.58    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f234,plain,(
% 1.35/0.58    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f233,f146])).
% 1.35/0.58  fof(f146,plain,(
% 1.35/0.58    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.35/0.58    inference(forward_demodulation,[],[f78,f79])).
% 1.35/0.58  fof(f79,plain,(
% 1.35/0.58    sK5 = sK6),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f78,plain,(
% 1.35/0.58    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f233,plain,(
% 1.35/0.58    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(subsumption_resolution,[],[f232,f81])).
% 1.35/0.58  fof(f81,plain,(
% 1.35/0.58    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f232,plain,(
% 1.35/0.58    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~sP7(sK3,sK2,sK5)),
% 1.35/0.58    inference(resolution,[],[f209,f113])).
% 1.35/0.58  fof(f113,plain,(
% 1.35/0.58    ( ! [X4,X2,X0,X7,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP7(X3,X2,X7)) )),
% 1.35/0.58    inference(general_splitting,[],[f108,f112_D])).
% 1.35/0.58  fof(f108,plain,(
% 1.35/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.58    inference(equality_resolution,[],[f93])).
% 1.35/0.58  fof(f93,plain,(
% 1.35/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f59])).
% 1.35/0.58  fof(f59,plain,(
% 1.35/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.58    inference(nnf_transformation,[],[f37])).
% 1.35/0.58  fof(f37,plain,(
% 1.35/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.58    inference(flattening,[],[f36])).
% 1.35/0.58  fof(f36,plain,(
% 1.35/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.58    inference(ennf_transformation,[],[f19])).
% 1.35/0.58  fof(f19,axiom,(
% 1.35/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 1.35/0.58  fof(f209,plain,(
% 1.35/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.35/0.58    inference(forward_demodulation,[],[f80,f79])).
% 1.35/0.58  fof(f80,plain,(
% 1.35/0.58    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.35/0.58    inference(cnf_transformation,[],[f57])).
% 1.35/0.58  fof(f213,plain,(
% 1.35/0.58    spl9_5),
% 1.35/0.58    inference(avatar_contradiction_clause,[],[f212])).
% 1.35/0.58  fof(f212,plain,(
% 1.35/0.58    $false | spl9_5),
% 1.35/0.58    inference(subsumption_resolution,[],[f210,f123])).
% 1.35/0.58  fof(f210,plain,(
% 1.35/0.58    ~l1_pre_topc(sK2) | spl9_5),
% 1.35/0.58    inference(resolution,[],[f179,f85])).
% 1.35/0.58  fof(f85,plain,(
% 1.35/0.58    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f27])).
% 1.35/0.58  fof(f27,plain,(
% 1.35/0.58    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.35/0.58    inference(ennf_transformation,[],[f11])).
% 1.35/0.58  fof(f11,axiom,(
% 1.35/0.58    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.35/0.58  fof(f179,plain,(
% 1.35/0.58    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | spl9_5),
% 1.35/0.58    inference(avatar_component_clause,[],[f177])).
% 1.35/0.58  fof(f183,plain,(
% 1.35/0.58    ~spl9_5 | spl9_6),
% 1.35/0.58    inference(avatar_split_clause,[],[f171,f181,f177])).
% 1.35/0.58  fof(f171,plain,(
% 1.35/0.58    ( ! [X4,X5] : (sK3 != g1_pre_topc(X4,X5) | u1_struct_0(sK2) = X4 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 1.35/0.58    inference(superposition,[],[f100,f76])).
% 1.35/0.58  fof(f100,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f47])).
% 1.35/0.58  fof(f47,plain,(
% 1.35/0.58    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.35/0.58    inference(ennf_transformation,[],[f13])).
% 1.35/0.58  fof(f13,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.35/0.58  fof(f164,plain,(
% 1.35/0.58    ~spl9_4),
% 1.35/0.58    inference(avatar_contradiction_clause,[],[f163])).
% 1.35/0.58  fof(f163,plain,(
% 1.35/0.58    $false | ~spl9_4),
% 1.35/0.58    inference(subsumption_resolution,[],[f162,f69])).
% 1.35/0.58  fof(f162,plain,(
% 1.35/0.58    v2_struct_0(sK2) | ~spl9_4),
% 1.35/0.58    inference(subsumption_resolution,[],[f161,f132])).
% 1.35/0.58  fof(f132,plain,(
% 1.35/0.58    l1_struct_0(sK2)),
% 1.35/0.58    inference(resolution,[],[f123,f83])).
% 1.35/0.58  fof(f161,plain,(
% 1.35/0.58    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl9_4),
% 1.35/0.58    inference(resolution,[],[f159,f90])).
% 1.35/0.58  fof(f90,plain,(
% 1.35/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f33])).
% 1.35/0.58  fof(f33,plain,(
% 1.35/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.35/0.58    inference(flattening,[],[f32])).
% 1.35/0.58  fof(f32,plain,(
% 1.35/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.35/0.58    inference(ennf_transformation,[],[f12])).
% 1.35/0.58  fof(f12,axiom,(
% 1.35/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.35/0.58  fof(f159,plain,(
% 1.35/0.58    v1_xboole_0(u1_struct_0(sK2)) | ~spl9_4),
% 1.35/0.58    inference(avatar_component_clause,[],[f157])).
% 1.35/0.58  fof(f157,plain,(
% 1.35/0.58    spl9_4 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.35/0.58  fof(f160,plain,(
% 1.35/0.58    spl9_3 | spl9_4),
% 1.35/0.58    inference(avatar_split_clause,[],[f151,f157,f153])).
% 1.35/0.58  fof(f151,plain,(
% 1.35/0.58    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK5,u1_struct_0(sK2))),
% 1.35/0.58    inference(resolution,[],[f146,f97])).
% 1.35/0.58  fof(f97,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f45])).
% 1.35/0.58  fof(f45,plain,(
% 1.35/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.35/0.58    inference(flattening,[],[f44])).
% 1.35/0.58  fof(f44,plain,(
% 1.35/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.35/0.58    inference(ennf_transformation,[],[f2])).
% 1.35/0.58  fof(f2,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.35/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.35/0.58  % SZS output end Proof for theBenchmark
% 1.35/0.58  % (14799)------------------------------
% 1.35/0.58  % (14799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (14799)Termination reason: Refutation
% 1.35/0.58  
% 1.35/0.58  % (14799)Memory used [KB]: 11001
% 1.35/0.58  % (14799)Time elapsed: 0.150 s
% 1.35/0.58  % (14799)------------------------------
% 1.35/0.58  % (14799)------------------------------
% 1.35/0.58  % (14795)Success in time 0.211 s
%------------------------------------------------------------------------------
