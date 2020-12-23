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
% DateTime   : Thu Dec  3 13:18:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  311 (16203 expanded)
%              Number of leaves         :   22 (8916 expanded)
%              Depth                    :   47
%              Number of atoms          : 1939 (285477 expanded)
%              Number of equality atoms :  117 (21480 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2095,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f486,f488,f490,f2078])).

fof(f2078,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f2066,f78])).

fof(f78,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(superposition,[],[f60,f58])).

fof(f58,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
    & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f39,f38,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                                & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6)
                            & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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
                          ( ~ r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6)
                          & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6)
                        & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6)
                      & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6)
                    & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6)
                  & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6)
                & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6)
              & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6)
            & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6)
          & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6)
        & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)
      & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6)
                              & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                      & X5 = X6 )
                                   => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5)
                                    & X5 = X6 )
                                 => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).

fof(f60,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f2066,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_4 ),
    inference(superposition,[],[f496,f1846])).

fof(f1846,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(subsumption_resolution,[],[f1845,f1752])).

fof(f1752,plain,(
    v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(superposition,[],[f619,f881])).

fof(f881,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(forward_demodulation,[],[f880,f607])).

fof(f607,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) ),
    inference(superposition,[],[f382,f452])).

fof(f452,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f451,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f451,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f450,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f450,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f449,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f449,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f345,f79])).

fof(f79,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f61,f44])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f345,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f344,f331])).

fof(f331,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f330,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f330,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f329,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f329,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f328,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f328,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f327,f52])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f327,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f326,f53])).

fof(f53,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f326,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f114,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f113,plain,(
    ! [X2,X3] :
      ( k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f112,plain,(
    ! [X2,X3] :
      ( k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f44])).

fof(f107,plain,(
    ! [X2,X3] :
      ( k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
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
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
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
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f344,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f343,f45])).

fof(f343,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f342,f46])).

fof(f342,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f341,f47])).

fof(f341,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f340,f52])).

fof(f340,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f339,f53])).

fof(f339,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f135,f54])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3))
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK0,X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f132,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK0,X1)
      | m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f68,f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f132,plain,(
    ! [X4,X5,X3] :
      ( k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(sK3,X3)
      | ~ m1_pre_topc(sK0,X3)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f382,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f381,f45])).

fof(f381,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f380,f46])).

fof(f380,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f379,f47])).

fof(f379,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f378,f227])).

fof(f227,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f226,f42])).

fof(f226,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f225,f43])).

fof(f225,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f44])).

fof(f224,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f79])).

fof(f215,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f105,f51])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f52])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f53])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f71,f54])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f378,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f368,f281])).

fof(f281,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f280,f42])).

fof(f280,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f279,f43])).

fof(f279,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f278,f44])).

fof(f278,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f269,f79])).

fof(f269,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f123,f51])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f118,f53])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f368,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f315,f117])).

fof(f117,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,(
    ! [X4,X5] :
      ( k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f115,f92])).

fof(f92,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f91,f43])).

fof(f91,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f67,f51])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f115,plain,(
    ! [X4,X5] :
      ( k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f108,f85])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f108,plain,(
    ! [X4,X5] :
      ( k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f65,f55])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f315,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f314,f42])).

fof(f314,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f313,f43])).

fof(f313,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f44])).

fof(f312,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f302,f79])).

fof(f302,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f51])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f127,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f47])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f125,f52])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f124,f53])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f73,f54])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f880,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(forward_demodulation,[],[f879,f452])).

fof(f879,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f878,f42])).

fof(f878,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f877,f43])).

fof(f877,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f875,f44])).

fof(f875,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f377,f51])).

fof(f377,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f376,f45])).

fof(f376,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f375,f46])).

fof(f375,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f374,f47])).

fof(f374,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f373,f227])).

fof(f373,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f367,f281])).

fof(f367,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f315,f136])).

fof(f136,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
      | k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2))
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f133,f95])).

fof(f95,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK3,X2)
      | m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f68,f55])).

fof(f133,plain,(
    ! [X6,X8,X7] :
      ( k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7))))
      | ~ v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7))
      | ~ v1_funct_1(X8)
      | ~ m1_pre_topc(sK2,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f63,f55])).

fof(f619,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(forward_demodulation,[],[f618,f452])).

fof(f618,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) ),
    inference(subsumption_resolution,[],[f617,f42])).

fof(f617,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f616,f43])).

fof(f616,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f615,f44])).

fof(f615,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f608,f51])).

fof(f608,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f397,f49])).

fof(f49,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f397,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X6,X5)
      | v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f396,f45])).

fof(f396,plain,(
    ! [X6,X5] :
      ( v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(sK3,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f395,f46])).

fof(f395,plain,(
    ! [X6,X5] :
      ( v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f394,f47])).

fof(f394,plain,(
    ! [X6,X5] :
      ( v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f393,f227])).

fof(f393,plain,(
    ! [X6,X5] :
      ( v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f371,f281])).

fof(f371,plain,(
    ! [X6,X5] :
      ( v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X6,X5)
      | ~ m1_pre_topc(sK3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f315,f71])).

fof(f1845,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(subsumption_resolution,[],[f1844,f1751])).

fof(f1751,plain,(
    v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f736,f881])).

fof(f736,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f735,f452])).

fof(f735,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f734,f42])).

fof(f734,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f733,f43])).

fof(f733,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f732,f44])).

fof(f732,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f725,f51])).

fof(f725,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f392,f49])).

fof(f392,plain,(
    ! [X4,X3] :
      ( ~ m1_pre_topc(X4,X3)
      | v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f391,f45])).

fof(f391,plain,(
    ! [X4,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(sK3,X3)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f390,f46])).

fof(f390,plain,(
    ! [X4,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f389,f47])).

fof(f389,plain,(
    ! [X4,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f388,f227])).

fof(f388,plain,(
    ! [X4,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f370,f281])).

fof(f370,plain,(
    ! [X4,X3] :
      ( v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(sK3,X3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f315,f72])).

fof(f1844,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(subsumption_resolution,[],[f1843,f1750])).

fof(f1750,plain,(
    m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f827,f881])).

fof(f827,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f826,f452])).

fof(f826,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f825,f42])).

fof(f825,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f824,f43])).

fof(f824,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f823,f44])).

fof(f823,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f816,f51])).

fof(f816,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f387,f49])).

fof(f387,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f386,f45])).

fof(f386,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f385,f46])).

fof(f385,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f384,f47])).

fof(f384,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f383,f227])).

fof(f383,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f369,f281])).

fof(f369,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f315,f73])).

fof(f1843,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(subsumption_resolution,[],[f1842,f455])).

fof(f455,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(superposition,[],[f223,f448])).

fof(f448,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f447,f42])).

fof(f447,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f43])).

fof(f446,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f445,f44])).

fof(f445,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f338,f79])).

fof(f338,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f337,f325])).

fof(f325,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f324,f45])).

fof(f324,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f323,f46])).

fof(f323,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f322,f47])).

fof(f322,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f321,f52])).

fof(f321,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f320,f53])).

fof(f320,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f111,f54])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f110,f42])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f44])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f65,f49])).

fof(f337,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f336,f45])).

fof(f336,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f335,f46])).

fof(f335,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f334,f47])).

fof(f334,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f333,f52])).

fof(f333,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f332,f53])).

fof(f332,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f134,f54])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f131,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f68,f49])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f63,f49])).

fof(f223,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f222,f42])).

fof(f222,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f43])).

fof(f221,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f220,f44])).

fof(f220,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f79])).

fof(f214,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f105,f49])).

fof(f1842,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(subsumption_resolution,[],[f1841,f454])).

fof(f454,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f277,f448])).

fof(f277,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f276,f42])).

fof(f276,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f275,f43])).

fof(f275,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f274,f44])).

fof(f274,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f268,f79])).

fof(f268,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f123,f49])).

fof(f1841,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(subsumption_resolution,[],[f1827,f453])).

fof(f453,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f311,f448])).

fof(f311,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f310,f42])).

fof(f310,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f43])).

fof(f309,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f308,f44])).

fof(f308,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f301,f79])).

fof(f301,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f49])).

fof(f1827,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)) ),
    inference(resolution,[],[f1042,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f1042,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f1041,f881])).

fof(f1041,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(subsumption_resolution,[],[f1040,f42])).

fof(f1040,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1039,f43])).

fof(f1039,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1038,f44])).

fof(f1038,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1037,f45])).

fof(f1037,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1036,f46])).

fof(f1036,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1035,f47])).

fof(f1035,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1034,f51])).

fof(f1034,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1033,f52])).

fof(f1033,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1032,f53])).

fof(f1032,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1031,f54])).

fof(f1031,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1030,f484])).

fof(f484,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(superposition,[],[f227,f452])).

fof(f1030,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1029,f483])).

fof(f483,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(superposition,[],[f281,f452])).

fof(f1029,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1013,f482])).

fof(f482,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f315,f452])).

fof(f1013,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f549,f172])).

fof(f172,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3))
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8))))
      | ~ v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
      | ~ v1_funct_1(X11)
      | ~ m1_pre_topc(sK3,X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f171,f95])).

fof(f171,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8))))
      | ~ v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
      | ~ v1_funct_1(X11)
      | ~ m1_pre_topc(sK2,X9)
      | ~ m1_pre_topc(sK3,X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f170,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8))))
      | ~ v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
      | ~ v1_funct_1(X11)
      | ~ m1_pre_topc(sK2,X9)
      | ~ m1_pre_topc(sK3,X9)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f163,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f163,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2))
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8))))
      | ~ v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8))
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
      | ~ v1_funct_1(X11)
      | ~ m1_pre_topc(sK2,X9)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK3,X9)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f64,f55])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_pre_topc(X3,X2)
      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).

fof(f549,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(superposition,[],[f399,f452])).

fof(f399,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f398,f227])).

fof(f398,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f372,f281])).

fof(f372,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(resolution,[],[f315,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f496,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f495,f55])).

fof(f495,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f492,f48])).

fof(f492,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(resolution,[],[f159,f77])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f57,f58])).

fof(f57,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_4
  <=> ! [X0] :
        ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f490,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f484,f148])).

fof(f148,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_1
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f488,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f483,f152])).

fof(f152,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_2
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f486,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f482,f156])).

fof(f156,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_3
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f160,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f144,f158,f154,f150,f146])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ) ),
    inference(subsumption_resolution,[],[f143,f45])).

fof(f143,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f142,f46])).

fof(f142,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f141,f47])).

fof(f141,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f140,f50])).

fof(f140,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f139,f92])).

fof(f139,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f138,f85])).

fof(f138,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f137,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f40])).

fof(f137,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
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
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:15:55 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (15316)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.49  % (15324)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.50  % (15306)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.50  % (15307)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.51  % (15308)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (15310)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (15317)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.52  % (15321)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (15306)Refutation not found, incomplete strategy% (15306)------------------------------
% 0.23/0.52  % (15306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (15306)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (15306)Memory used [KB]: 10618
% 0.23/0.52  % (15306)Time elapsed: 0.095 s
% 0.23/0.52  % (15306)------------------------------
% 0.23/0.52  % (15306)------------------------------
% 0.23/0.52  % (15329)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.52  % (15315)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (15311)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.53  % (15313)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.53  % (15309)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (15314)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (15312)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (15328)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (15330)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.53  % (15326)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.54  % (15327)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.54  % (15320)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.54  % (15331)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.55  % (15322)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.55  % (15319)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (15318)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.55  % (15323)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.55  % (15316)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (15325)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.57  % SZS output start Proof for theBenchmark
% 0.23/0.57  fof(f2095,plain,(
% 0.23/0.57    $false),
% 0.23/0.57    inference(avatar_sat_refutation,[],[f160,f486,f488,f490,f2078])).
% 0.23/0.57  fof(f2078,plain,(
% 0.23/0.57    ~spl7_4),
% 0.23/0.57    inference(avatar_contradiction_clause,[],[f2077])).
% 0.23/0.57  fof(f2077,plain,(
% 0.23/0.57    $false | ~spl7_4),
% 0.23/0.57    inference(subsumption_resolution,[],[f2066,f78])).
% 0.23/0.57  fof(f78,plain,(
% 0.23/0.57    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 0.23/0.57    inference(superposition,[],[f60,f58])).
% 0.23/0.57  fof(f58,plain,(
% 0.23/0.57    sK5 = sK6),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f40,plain,(
% 0.23/0.57    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f14,f39,f38,f37,f36,f35,f34,f33])).
% 0.23/0.57  fof(f33,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f34,plain,(
% 0.23/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f35,plain,(
% 0.23/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f36,plain,(
% 0.23/0.57    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f37,plain,(
% 0.23/0.57    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f38,plain,(
% 0.23/0.57    ? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f39,plain,(
% 0.23/0.57    ? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.23/0.57    introduced(choice_axiom,[])).
% 0.23/0.57  fof(f14,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.57    inference(flattening,[],[f13])).
% 0.23/0.57  fof(f13,plain,(
% 0.23/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f12])).
% 0.23/0.57  fof(f12,negated_conjecture,(
% 0.23/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 0.23/0.57    inference(negated_conjecture,[],[f11])).
% 0.23/0.57  fof(f11,conjecture,(
% 0.23/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).
% 0.23/0.57  fof(f60,plain,(
% 0.23/0.57    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f2066,plain,(
% 0.23/0.57    r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~spl7_4),
% 0.23/0.57    inference(superposition,[],[f496,f1846])).
% 0.23/0.57  fof(f1846,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)),
% 0.23/0.57    inference(subsumption_resolution,[],[f1845,f1752])).
% 0.23/0.57  fof(f1752,plain,(
% 0.23/0.57    v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 0.23/0.57    inference(superposition,[],[f619,f881])).
% 0.23/0.57  fof(f881,plain,(
% 0.23/0.57    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))),
% 0.23/0.57    inference(forward_demodulation,[],[f880,f607])).
% 0.23/0.57  fof(f607,plain,(
% 0.23/0.57    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2))),
% 0.23/0.57    inference(superposition,[],[f382,f452])).
% 0.23/0.57  fof(f452,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),
% 0.23/0.57    inference(subsumption_resolution,[],[f451,f42])).
% 0.23/0.57  fof(f42,plain,(
% 0.23/0.57    ~v2_struct_0(sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f451,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f450,f43])).
% 0.23/0.57  fof(f43,plain,(
% 0.23/0.57    v2_pre_topc(sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f450,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f449,f44])).
% 0.23/0.57  fof(f44,plain,(
% 0.23/0.57    l1_pre_topc(sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f449,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f345,f79])).
% 0.23/0.57  fof(f79,plain,(
% 0.23/0.57    m1_pre_topc(sK0,sK0)),
% 0.23/0.57    inference(resolution,[],[f61,f44])).
% 0.23/0.57  fof(f61,plain,(
% 0.23/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f15])).
% 0.23/0.57  fof(f15,plain,(
% 0.23/0.57    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f7])).
% 0.23/0.57  fof(f7,axiom,(
% 0.23/0.57    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.23/0.57  fof(f345,plain,(
% 0.23/0.57    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(forward_demodulation,[],[f344,f331])).
% 0.23/0.57  fof(f331,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 0.23/0.57    inference(subsumption_resolution,[],[f330,f45])).
% 0.23/0.57  fof(f45,plain,(
% 0.23/0.57    ~v2_struct_0(sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f330,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f329,f46])).
% 0.23/0.57  fof(f46,plain,(
% 0.23/0.57    v2_pre_topc(sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f329,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f328,f47])).
% 0.23/0.57  fof(f47,plain,(
% 0.23/0.57    l1_pre_topc(sK1)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f328,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f327,f52])).
% 0.23/0.57  fof(f52,plain,(
% 0.23/0.57    v1_funct_1(sK4)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f327,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f326,f53])).
% 0.23/0.57  fof(f53,plain,(
% 0.23/0.57    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f326,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(resolution,[],[f114,f54])).
% 0.23/0.57  fof(f54,plain,(
% 0.23/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f114,plain,(
% 0.23/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f113,f42])).
% 0.23/0.57  fof(f113,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f112,f43])).
% 0.23/0.57  fof(f112,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f107,f44])).
% 0.23/0.57  fof(f107,plain,(
% 0.23/0.57    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.57    inference(resolution,[],[f65,f51])).
% 0.23/0.57  fof(f51,plain,(
% 0.23/0.57    m1_pre_topc(sK3,sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f65,plain,(
% 0.23/0.57    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f22])).
% 0.23/0.57  fof(f22,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.57    inference(flattening,[],[f21])).
% 0.23/0.57  fof(f21,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f4])).
% 0.23/0.57  fof(f4,axiom,(
% 0.23/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.23/0.57  fof(f344,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f343,f45])).
% 0.23/0.57  fof(f343,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f342,f46])).
% 0.23/0.57  fof(f342,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f341,f47])).
% 0.23/0.57  fof(f341,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f340,f52])).
% 0.23/0.57  fof(f340,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f339,f53])).
% 0.23/0.57  fof(f339,plain,(
% 0.23/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(resolution,[],[f135,f54])).
% 0.23/0.57  fof(f135,plain,(
% 0.23/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f132,f94])).
% 0.23/0.57  fof(f94,plain,(
% 0.23/0.57    ( ! [X1] : (~m1_pre_topc(sK0,X1) | m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.57    inference(resolution,[],[f68,f51])).
% 0.23/0.57  fof(f68,plain,(
% 0.23/0.57    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f28])).
% 0.23/0.57  fof(f28,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.57    inference(flattening,[],[f27])).
% 0.23/0.57  fof(f27,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f10])).
% 0.23/0.57  fof(f10,axiom,(
% 0.23/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.23/0.57  fof(f132,plain,(
% 0.23/0.57    ( ! [X4,X5,X3] : (k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.23/0.57    inference(resolution,[],[f63,f51])).
% 0.23/0.57  fof(f63,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f18])).
% 0.23/0.57  fof(f18,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.57    inference(flattening,[],[f17])).
% 0.23/0.57  fof(f17,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f5])).
% 0.23/0.57  fof(f5,axiom,(
% 0.23/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.23/0.57  fof(f382,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)),
% 0.23/0.57    inference(subsumption_resolution,[],[f381,f45])).
% 0.23/0.57  fof(f381,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f380,f46])).
% 0.23/0.57  fof(f380,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f379,f47])).
% 0.23/0.57  fof(f379,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f378,f227])).
% 0.23/0.57  fof(f227,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 0.23/0.57    inference(subsumption_resolution,[],[f226,f42])).
% 0.23/0.57  fof(f226,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f225,f43])).
% 0.23/0.57  fof(f225,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f224,f44])).
% 0.23/0.57  fof(f224,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f215,f79])).
% 0.23/0.57  fof(f215,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f105,f51])).
% 0.23/0.57  fof(f105,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f104,f45])).
% 0.23/0.57  fof(f104,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f103,f46])).
% 0.23/0.57  fof(f103,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f102,f47])).
% 0.23/0.57  fof(f102,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f101,f52])).
% 0.23/0.57  fof(f101,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f100,f53])).
% 0.23/0.57  fof(f100,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(resolution,[],[f71,f54])).
% 0.23/0.57  fof(f71,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f32,plain,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.57    inference(flattening,[],[f31])).
% 0.23/0.57  fof(f31,plain,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f6])).
% 0.23/0.57  fof(f6,axiom,(
% 0.23/0.57    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 0.23/0.57  fof(f378,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(subsumption_resolution,[],[f368,f281])).
% 0.23/0.57  fof(f281,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.23/0.57    inference(subsumption_resolution,[],[f280,f42])).
% 0.23/0.57  fof(f280,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f279,f43])).
% 0.23/0.57  fof(f279,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f278,f44])).
% 0.23/0.57  fof(f278,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f269,f79])).
% 0.23/0.57  fof(f269,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f123,f51])).
% 0.23/0.57  fof(f123,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f122,f45])).
% 0.23/0.57  fof(f122,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f121,f46])).
% 0.23/0.57  fof(f121,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f120,f47])).
% 0.23/0.57  fof(f120,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f119,f52])).
% 0.23/0.57  fof(f119,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f118,f53])).
% 0.23/0.57  fof(f118,plain,(
% 0.23/0.57    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(resolution,[],[f72,f54])).
% 0.23/0.57  fof(f72,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f368,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 0.23/0.57    inference(resolution,[],[f315,f117])).
% 0.23/0.57  fof(f117,plain,(
% 0.23/0.57    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f116,f50])).
% 0.23/0.57  fof(f50,plain,(
% 0.23/0.57    ~v2_struct_0(sK3)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f116,plain,(
% 0.23/0.57    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v2_struct_0(sK3)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f115,f92])).
% 0.23/0.57  fof(f92,plain,(
% 0.23/0.57    v2_pre_topc(sK3)),
% 0.23/0.57    inference(subsumption_resolution,[],[f91,f43])).
% 0.23/0.57  fof(f91,plain,(
% 0.23/0.57    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f87,f44])).
% 0.23/0.57  fof(f87,plain,(
% 0.23/0.57    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.23/0.57    inference(resolution,[],[f67,f51])).
% 0.23/0.57  fof(f67,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f26])).
% 0.23/0.57  fof(f26,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.57    inference(flattening,[],[f25])).
% 0.23/0.57  fof(f25,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.57    inference(ennf_transformation,[],[f2])).
% 0.23/0.57  fof(f2,axiom,(
% 0.23/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.23/0.57  fof(f115,plain,(
% 0.23/0.57    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f108,f85])).
% 0.23/0.57  fof(f85,plain,(
% 0.23/0.57    l1_pre_topc(sK3)),
% 0.23/0.57    inference(subsumption_resolution,[],[f82,f44])).
% 0.23/0.57  fof(f82,plain,(
% 0.23/0.57    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.23/0.57    inference(resolution,[],[f62,f51])).
% 0.23/0.57  fof(f62,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f16])).
% 0.23/0.57  fof(f16,plain,(
% 0.23/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.57    inference(ennf_transformation,[],[f3])).
% 0.23/0.57  fof(f3,axiom,(
% 0.23/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.57  fof(f108,plain,(
% 0.23/0.57    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.23/0.57    inference(resolution,[],[f65,f55])).
% 0.23/0.57  fof(f55,plain,(
% 0.23/0.57    m1_pre_topc(sK2,sK3)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f315,plain,(
% 0.23/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.23/0.57    inference(subsumption_resolution,[],[f314,f42])).
% 0.23/0.57  fof(f314,plain,(
% 0.23/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f313,f43])).
% 0.23/0.57  fof(f313,plain,(
% 0.23/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f312,f44])).
% 0.23/0.57  fof(f312,plain,(
% 0.23/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f302,f79])).
% 0.23/0.57  fof(f302,plain,(
% 0.23/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f129,f51])).
% 0.23/0.57  fof(f129,plain,(
% 0.23/0.57    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f128,f45])).
% 0.23/0.57  fof(f128,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f127,f46])).
% 0.23/0.57  fof(f127,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f126,f47])).
% 0.23/0.57  fof(f126,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f125,f52])).
% 0.23/0.57  fof(f125,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f124,f53])).
% 0.23/0.57  fof(f124,plain,(
% 0.23/0.57    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(resolution,[],[f73,f54])).
% 0.23/0.57  fof(f73,plain,(
% 0.23/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(cnf_transformation,[],[f32])).
% 0.23/0.57  fof(f880,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))),
% 0.23/0.57    inference(forward_demodulation,[],[f879,f452])).
% 0.23/0.57  fof(f879,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 0.23/0.57    inference(subsumption_resolution,[],[f878,f42])).
% 0.23/0.57  fof(f878,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f877,f43])).
% 0.23/0.57  fof(f877,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f875,f44])).
% 0.23/0.57  fof(f875,plain,(
% 0.23/0.57    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f377,f51])).
% 0.23/0.57  fof(f377,plain,(
% 0.23/0.57    ( ! [X0] : (~m1_pre_topc(sK3,X0) | k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f376,f45])).
% 0.23/0.57  fof(f376,plain,(
% 0.23/0.57    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f375,f46])).
% 0.23/0.57  fof(f375,plain,(
% 0.23/0.57    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f374,f47])).
% 0.23/0.57  fof(f374,plain,(
% 0.23/0.57    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f373,f227])).
% 0.23/0.57  fof(f373,plain,(
% 0.23/0.57    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f367,f281])).
% 0.23/0.57  fof(f367,plain,(
% 0.23/0.57    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.57    inference(resolution,[],[f315,f136])).
% 0.23/0.57  fof(f136,plain,(
% 0.23/0.57    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7)))) | k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2)) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f133,f95])).
% 0.23/0.57  fof(f95,plain,(
% 0.23/0.57    ( ! [X2] : (~m1_pre_topc(sK3,X2) | m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 0.23/0.57    inference(resolution,[],[f68,f55])).
% 0.23/0.57  fof(f133,plain,(
% 0.23/0.57    ( ! [X6,X8,X7] : (k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(sK2,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 0.23/0.57    inference(resolution,[],[f63,f55])).
% 0.23/0.57  fof(f619,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 0.23/0.57    inference(forward_demodulation,[],[f618,f452])).
% 0.23/0.57  fof(f618,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))),
% 0.23/0.57    inference(subsumption_resolution,[],[f617,f42])).
% 0.23/0.57  fof(f617,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f616,f43])).
% 0.23/0.57  fof(f616,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f615,f44])).
% 0.23/0.57  fof(f615,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f608,f51])).
% 0.23/0.57  fof(f608,plain,(
% 0.23/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f397,f49])).
% 0.23/0.57  fof(f49,plain,(
% 0.23/0.57    m1_pre_topc(sK2,sK0)),
% 0.23/0.57    inference(cnf_transformation,[],[f40])).
% 0.23/0.57  fof(f397,plain,(
% 0.23/0.57    ( ! [X6,X5] : (~m1_pre_topc(X6,X5) | v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f396,f45])).
% 0.23/0.57  fof(f396,plain,(
% 0.23/0.57    ( ! [X6,X5] : (v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(sK3,X5) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f395,f46])).
% 0.23/0.57  fof(f395,plain,(
% 0.23/0.57    ( ! [X6,X5] : (v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(sK3,X5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f394,f47])).
% 0.23/0.57  fof(f394,plain,(
% 0.23/0.57    ( ! [X6,X5] : (v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f393,f227])).
% 0.23/0.57  fof(f393,plain,(
% 0.23/0.57    ( ! [X6,X5] : (v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f371,f281])).
% 0.23/0.57  fof(f371,plain,(
% 0.23/0.57    ( ! [X6,X5] : (v1_funct_1(k3_tmap_1(X5,sK1,sK3,X6,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X6,X5) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 0.23/0.57    inference(resolution,[],[f315,f71])).
% 0.23/0.57  fof(f1845,plain,(
% 0.23/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 0.23/0.57    inference(subsumption_resolution,[],[f1844,f1751])).
% 0.23/0.57  fof(f1751,plain,(
% 0.23/0.57    v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.23/0.57    inference(superposition,[],[f736,f881])).
% 0.23/0.57  fof(f736,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.23/0.57    inference(forward_demodulation,[],[f735,f452])).
% 0.23/0.57  fof(f735,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.23/0.57    inference(subsumption_resolution,[],[f734,f42])).
% 0.23/0.57  fof(f734,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f733,f43])).
% 0.23/0.57  fof(f733,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f732,f44])).
% 0.23/0.57  fof(f732,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(subsumption_resolution,[],[f725,f51])).
% 0.23/0.57  fof(f725,plain,(
% 0.23/0.57    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.23/0.57    inference(resolution,[],[f392,f49])).
% 0.23/0.57  fof(f392,plain,(
% 0.23/0.57    ( ! [X4,X3] : (~m1_pre_topc(X4,X3) | v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.23/0.57    inference(subsumption_resolution,[],[f391,f45])).
% 1.59/0.57  fof(f391,plain,(
% 1.59/0.57    ( ! [X4,X3] : (v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f390,f46])).
% 1.59/0.57  fof(f390,plain,(
% 1.59/0.57    ( ! [X4,X3] : (v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f389,f47])).
% 1.59/0.57  fof(f389,plain,(
% 1.59/0.57    ( ! [X4,X3] : (v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f388,f227])).
% 1.59/0.57  fof(f388,plain,(
% 1.59/0.57    ( ! [X4,X3] : (v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f370,f281])).
% 1.59/0.57  fof(f370,plain,(
% 1.59/0.57    ( ! [X4,X3] : (v1_funct_2(k3_tmap_1(X3,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X4),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.59/0.57    inference(resolution,[],[f315,f72])).
% 1.59/0.57  fof(f1844,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 1.59/0.57    inference(subsumption_resolution,[],[f1843,f1750])).
% 1.59/0.57  fof(f1750,plain,(
% 1.59/0.57    m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.59/0.57    inference(superposition,[],[f827,f881])).
% 1.59/0.57  fof(f827,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.59/0.57    inference(forward_demodulation,[],[f826,f452])).
% 1.59/0.57  fof(f826,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.59/0.57    inference(subsumption_resolution,[],[f825,f42])).
% 1.59/0.57  fof(f825,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f824,f43])).
% 1.59/0.57  fof(f824,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f823,f44])).
% 1.59/0.57  fof(f823,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f816,f51])).
% 1.59/0.57  fof(f816,plain,(
% 1.59/0.57    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(resolution,[],[f387,f49])).
% 1.59/0.57  fof(f387,plain,(
% 1.59/0.57    ( ! [X2,X1] : (~m1_pre_topc(X2,X1) | m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f386,f45])).
% 1.59/0.57  fof(f386,plain,(
% 1.59/0.57    ( ! [X2,X1] : (m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f385,f46])).
% 1.59/0.57  fof(f385,plain,(
% 1.59/0.57    ( ! [X2,X1] : (m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f384,f47])).
% 1.59/0.57  fof(f384,plain,(
% 1.59/0.57    ( ! [X2,X1] : (m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f383,f227])).
% 1.59/0.57  fof(f383,plain,(
% 1.59/0.57    ( ! [X2,X1] : (m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f369,f281])).
% 1.59/0.57  fof(f369,plain,(
% 1.59/0.57    ( ! [X2,X1] : (m1_subset_1(k3_tmap_1(X1,sK1,sK3,X2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.59/0.57    inference(resolution,[],[f315,f73])).
% 1.59/0.57  fof(f1843,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 1.59/0.57    inference(subsumption_resolution,[],[f1842,f455])).
% 1.59/0.57  fof(f455,plain,(
% 1.59/0.57    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.59/0.57    inference(superposition,[],[f223,f448])).
% 1.59/0.57  fof(f448,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 1.59/0.57    inference(subsumption_resolution,[],[f447,f42])).
% 1.59/0.57  fof(f447,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f446,f43])).
% 1.59/0.57  fof(f446,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f445,f44])).
% 1.59/0.57  fof(f445,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(resolution,[],[f338,f79])).
% 1.59/0.57  fof(f338,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(forward_demodulation,[],[f337,f325])).
% 1.59/0.57  fof(f325,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.59/0.57    inference(subsumption_resolution,[],[f324,f45])).
% 1.59/0.57  fof(f324,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 1.59/0.57    inference(subsumption_resolution,[],[f323,f46])).
% 1.59/0.57  fof(f323,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.59/0.57    inference(subsumption_resolution,[],[f322,f47])).
% 1.59/0.57  fof(f322,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.59/0.57    inference(subsumption_resolution,[],[f321,f52])).
% 1.59/0.57  fof(f321,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.59/0.57    inference(subsumption_resolution,[],[f320,f53])).
% 1.59/0.57  fof(f320,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.59/0.57    inference(resolution,[],[f111,f54])).
% 1.59/0.57  fof(f111,plain,(
% 1.59/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f110,f42])).
% 1.59/0.57  fof(f110,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f109,f43])).
% 1.59/0.57  fof(f109,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f106,f44])).
% 1.59/0.57  fof(f106,plain,(
% 1.59/0.57    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.59/0.57    inference(resolution,[],[f65,f49])).
% 1.59/0.57  fof(f337,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f336,f45])).
% 1.59/0.57  fof(f336,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f335,f46])).
% 1.59/0.57  fof(f335,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f334,f47])).
% 1.59/0.57  fof(f334,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f333,f52])).
% 1.59/0.57  fof(f333,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f332,f53])).
% 1.59/0.57  fof(f332,plain,(
% 1.59/0.57    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(resolution,[],[f134,f54])).
% 1.59/0.57  fof(f134,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(subsumption_resolution,[],[f131,f93])).
% 1.59/0.57  fof(f93,plain,(
% 1.59/0.57    ( ! [X0] : (~m1_pre_topc(sK0,X0) | m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.57    inference(resolution,[],[f68,f49])).
% 1.59/0.57  fof(f131,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.57    inference(resolution,[],[f63,f49])).
% 1.59/0.57  fof(f223,plain,(
% 1.59/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.59/0.57    inference(subsumption_resolution,[],[f222,f42])).
% 1.59/0.57  fof(f222,plain,(
% 1.59/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f221,f43])).
% 1.59/0.57  fof(f221,plain,(
% 1.59/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f220,f44])).
% 1.59/0.57  fof(f220,plain,(
% 1.59/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(subsumption_resolution,[],[f214,f79])).
% 1.59/0.57  fof(f214,plain,(
% 1.59/0.57    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.57    inference(resolution,[],[f105,f49])).
% 1.59/0.57  fof(f1842,plain,(
% 1.59/0.57    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 1.59/0.57    inference(subsumption_resolution,[],[f1841,f454])).
% 1.59/0.57  fof(f454,plain,(
% 1.59/0.57    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.59/0.57    inference(superposition,[],[f277,f448])).
% 1.59/0.58  fof(f277,plain,(
% 1.59/0.58    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.59/0.58    inference(subsumption_resolution,[],[f276,f42])).
% 1.59/0.58  fof(f276,plain,(
% 1.59/0.58    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f275,f43])).
% 1.59/0.58  fof(f275,plain,(
% 1.59/0.58    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f274,f44])).
% 1.59/0.58  fof(f274,plain,(
% 1.59/0.58    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f268,f79])).
% 1.59/0.58  fof(f268,plain,(
% 1.59/0.58    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f123,f49])).
% 1.59/0.58  fof(f1841,plain,(
% 1.59/0.58    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 1.59/0.58    inference(subsumption_resolution,[],[f1827,f453])).
% 1.59/0.58  fof(f453,plain,(
% 1.59/0.58    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.59/0.58    inference(superposition,[],[f311,f448])).
% 1.59/0.58  fof(f311,plain,(
% 1.59/0.58    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.59/0.58    inference(subsumption_resolution,[],[f310,f42])).
% 1.59/0.58  fof(f310,plain,(
% 1.59/0.58    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f309,f43])).
% 1.59/0.58  fof(f309,plain,(
% 1.59/0.58    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f308,f44])).
% 1.59/0.58  fof(f308,plain,(
% 1.59/0.58    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f301,f79])).
% 1.59/0.58  fof(f301,plain,(
% 1.59/0.58    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f129,f49])).
% 1.59/0.58  fof(f1827,plain,(
% 1.59/0.58    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2))),
% 1.59/0.58    inference(resolution,[],[f1042,f69])).
% 1.59/0.58  fof(f69,plain,(
% 1.59/0.58    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.59/0.58    inference(nnf_transformation,[],[f30])).
% 1.59/0.58  fof(f30,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.59/0.58    inference(flattening,[],[f29])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.59/0.58    inference(ennf_transformation,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.59/0.58  fof(f1042,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.59/0.58    inference(forward_demodulation,[],[f1041,f881])).
% 1.59/0.58  fof(f1041,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.59/0.58    inference(subsumption_resolution,[],[f1040,f42])).
% 1.59/0.58  fof(f1040,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1039,f43])).
% 1.59/0.58  fof(f1039,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1038,f44])).
% 1.59/0.58  fof(f1038,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1037,f45])).
% 1.59/0.58  fof(f1037,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1036,f46])).
% 1.59/0.58  fof(f1036,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1035,f47])).
% 1.59/0.58  fof(f1035,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1034,f51])).
% 1.59/0.58  fof(f1034,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1033,f52])).
% 1.59/0.58  fof(f1033,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1032,f53])).
% 1.59/0.58  fof(f1032,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1031,f54])).
% 1.59/0.58  fof(f1031,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1030,f484])).
% 1.59/0.58  fof(f484,plain,(
% 1.59/0.58    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.59/0.58    inference(superposition,[],[f227,f452])).
% 1.59/0.58  fof(f1030,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1029,f483])).
% 1.59/0.58  fof(f483,plain,(
% 1.59/0.58    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.59/0.58    inference(superposition,[],[f281,f452])).
% 1.59/0.58  fof(f1029,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f1013,f482])).
% 1.59/0.58  fof(f482,plain,(
% 1.59/0.58    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.59/0.58    inference(superposition,[],[f315,f452])).
% 1.59/0.58  fof(f1013,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f549,f172])).
% 1.59/0.58  fof(f172,plain,(
% 1.59/0.58    ( ! [X10,X8,X11,X9] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3)) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8)))) | ~v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8)) | ~v1_funct_1(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8)))) | ~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8)) | ~v1_funct_1(X11) | ~m1_pre_topc(sK3,X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f171,f95])).
% 1.59/0.58  fof(f171,plain,(
% 1.59/0.58    ( ! [X10,X8,X11,X9] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2)) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8)))) | ~v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8)) | ~v1_funct_1(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8)))) | ~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8)) | ~v1_funct_1(X11) | ~m1_pre_topc(sK2,X9) | ~m1_pre_topc(sK3,X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f170,f50])).
% 1.59/0.58  fof(f170,plain,(
% 1.59/0.58    ( ! [X10,X8,X11,X9] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2)) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8)))) | ~v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8)) | ~v1_funct_1(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8)))) | ~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8)) | ~v1_funct_1(X11) | ~m1_pre_topc(sK2,X9) | ~m1_pre_topc(sK3,X9) | v2_struct_0(sK3) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f163,f48])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    ~v2_struct_0(sK2)),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f163,plain,(
% 1.59/0.58    ( ! [X10,X8,X11,X9] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X8),k3_tmap_1(X9,X8,sK3,sK2,X10),k2_tmap_1(X9,X8,X11,sK2)) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X8),X10,k2_tmap_1(X9,X8,X11,sK3)) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X8)))) | ~v1_funct_2(X10,u1_struct_0(sK3),u1_struct_0(X8)) | ~v1_funct_1(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8)))) | ~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8)) | ~v1_funct_1(X11) | ~m1_pre_topc(sK2,X9) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,X9) | v2_struct_0(sK3) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9)) )),
% 1.59/0.58    inference(resolution,[],[f64,f55])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_pre_topc(X3,X2) | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f20])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f19])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).
% 1.59/0.58  fof(f549,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.59/0.58    inference(superposition,[],[f399,f452])).
% 1.59/0.58  fof(f399,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 1.59/0.58    inference(subsumption_resolution,[],[f398,f227])).
% 1.59/0.58  fof(f398,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 1.59/0.58    inference(subsumption_resolution,[],[f372,f281])).
% 1.59/0.58  fof(f372,plain,(
% 1.59/0.58    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 1.59/0.58    inference(resolution,[],[f315,f76])).
% 1.59/0.58  fof(f76,plain,(
% 1.59/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f75])).
% 1.59/0.58  fof(f75,plain,(
% 1.59/0.58    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.59/0.58    inference(equality_resolution,[],[f70])).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f41])).
% 1.59/0.58  fof(f496,plain,(
% 1.59/0.58    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 1.59/0.58    inference(subsumption_resolution,[],[f495,f55])).
% 1.59/0.58  fof(f495,plain,(
% 1.59/0.58    ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 1.59/0.58    inference(subsumption_resolution,[],[f492,f48])).
% 1.59/0.58  fof(f492,plain,(
% 1.59/0.58    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 1.59/0.58    inference(resolution,[],[f159,f77])).
% 1.59/0.58  fof(f77,plain,(
% 1.59/0.58    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.59/0.58    inference(forward_demodulation,[],[f57,f58])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f159,plain,(
% 1.59/0.58    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)) ) | ~spl7_4),
% 1.59/0.58    inference(avatar_component_clause,[],[f158])).
% 1.59/0.58  fof(f158,plain,(
% 1.59/0.58    spl7_4 <=> ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.59/0.58  fof(f490,plain,(
% 1.59/0.58    spl7_1),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f489])).
% 1.59/0.58  fof(f489,plain,(
% 1.59/0.58    $false | spl7_1),
% 1.59/0.58    inference(subsumption_resolution,[],[f484,f148])).
% 1.59/0.58  fof(f148,plain,(
% 1.59/0.58    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | spl7_1),
% 1.59/0.58    inference(avatar_component_clause,[],[f146])).
% 1.59/0.58  fof(f146,plain,(
% 1.59/0.58    spl7_1 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.59/0.58  fof(f488,plain,(
% 1.59/0.58    spl7_2),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f487])).
% 1.59/0.58  fof(f487,plain,(
% 1.59/0.58    $false | spl7_2),
% 1.59/0.58    inference(subsumption_resolution,[],[f483,f152])).
% 1.59/0.58  fof(f152,plain,(
% 1.59/0.58    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_2),
% 1.59/0.58    inference(avatar_component_clause,[],[f150])).
% 1.59/0.58  fof(f150,plain,(
% 1.59/0.58    spl7_2 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.59/0.58  fof(f486,plain,(
% 1.59/0.58    spl7_3),
% 1.59/0.58    inference(avatar_contradiction_clause,[],[f485])).
% 1.59/0.58  fof(f485,plain,(
% 1.59/0.58    $false | spl7_3),
% 1.59/0.58    inference(subsumption_resolution,[],[f482,f156])).
% 1.59/0.58  fof(f156,plain,(
% 1.59/0.58    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_3),
% 1.59/0.58    inference(avatar_component_clause,[],[f154])).
% 1.59/0.58  fof(f154,plain,(
% 1.59/0.58    spl7_3 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.59/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.59/0.58  fof(f160,plain,(
% 1.59/0.58    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4),
% 1.59/0.58    inference(avatar_split_clause,[],[f144,f158,f154,f150,f146])).
% 1.59/0.58  fof(f144,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f143,f45])).
% 1.59/0.58  fof(f143,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f142,f46])).
% 1.59/0.58  fof(f142,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f141,f47])).
% 1.59/0.58  fof(f141,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f140,f50])).
% 1.59/0.58  fof(f140,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f139,f92])).
% 1.59/0.58  fof(f139,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f138,f85])).
% 1.59/0.58  fof(f138,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f137,f56])).
% 1.59/0.58  fof(f56,plain,(
% 1.59/0.58    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f137,plain,(
% 1.59/0.58    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.59/0.58    inference(resolution,[],[f74,f59])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f74,plain,(
% 1.59/0.58    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(equality_resolution,[],[f66])).
% 1.59/0.58  fof(f66,plain,(
% 1.59/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.59/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (15316)------------------------------
% 1.59/0.58  % (15316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (15316)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (15316)Memory used [KB]: 11641
% 1.59/0.58  % (15316)Time elapsed: 0.124 s
% 1.59/0.58  % (15316)------------------------------
% 1.59/0.58  % (15316)------------------------------
% 1.59/0.58  % (15305)Success in time 0.205 s
%------------------------------------------------------------------------------
