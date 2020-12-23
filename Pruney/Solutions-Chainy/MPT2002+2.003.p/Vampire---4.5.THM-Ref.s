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
% DateTime   : Thu Dec  3 13:23:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  148 (2279 expanded)
%              Number of leaves         :   21 (1081 expanded)
%              Depth                    :   33
%              Number of atoms          :  847 (35615 expanded)
%              Number of equality atoms :  145 (7888 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f685,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f143,f150,f169,f684])).

fof(f684,plain,
    ( ~ spl12_2
    | ~ spl12_5 ),
    inference(avatar_contradiction_clause,[],[f683])).

fof(f683,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f682,f92])).

fof(f92,plain,(
    ~ sP0(sK5,sK6,sK4) ),
    inference(subsumption_resolution,[],[f91,f74])).

fof(f74,plain,(
    ~ v5_orders_3(sK6,sK4,sK5) ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f47,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v5_orders_3(sK7,sK4,sK5)
    & v5_orders_3(sK6,sK2,sK3)
    & sK6 = sK7
    & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & l1_orders_2(sK5)
    & l1_orders_2(sK4)
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f24,f23,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ v5_orders_3(X5,X2,X3)
                            & v5_orders_3(X4,X0,X1)
                            & X4 = X5
                            & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & l1_orders_2(X3) )
                & l1_orders_2(X2) )
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,sK2,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ v5_orders_3(X5,X2,X3)
                        & v5_orders_3(X4,sK2,X1)
                        & X4 = X5
                        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                        & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & l1_orders_2(X3) )
            & l1_orders_2(X2) )
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ v5_orders_3(X5,X2,X3)
                      & v5_orders_3(X4,sK2,sK3)
                      & X4 = X5
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
                      & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & l1_orders_2(X3) )
          & l1_orders_2(X2) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ v5_orders_3(X5,X2,X3)
                    & v5_orders_3(X4,sK2,sK3)
                    & X4 = X5
                    & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
                    & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & l1_orders_2(X3) )
        & l1_orders_2(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ v5_orders_3(X5,sK4,X3)
                  & v5_orders_3(X4,sK2,sK3)
                  & X4 = X5
                  & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
                  & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3))))
                  & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & l1_orders_2(X3) )
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ v5_orders_3(X5,sK4,X3)
                & v5_orders_3(X4,sK2,sK3)
                & X4 = X5
                & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
                & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3))))
                & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & l1_orders_2(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ v5_orders_3(X5,sK4,sK5)
              & v5_orders_3(X4,sK2,sK3)
              & X4 = X5
              & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
              & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
              & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ v5_orders_3(X5,sK4,sK5)
            & v5_orders_3(X4,sK2,sK3)
            & X4 = X5
            & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
            & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
            & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ v5_orders_3(X5,sK4,sK5)
          & v5_orders_3(sK6,sK2,sK3)
          & sK6 = X5
          & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
          & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
          & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5))
          & v1_funct_1(X5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X5] :
        ( ~ v5_orders_3(X5,sK4,sK5)
        & v5_orders_3(sK6,sK2,sK3)
        & sK6 = X5
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
        & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
        & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5))
        & v1_funct_1(X5) )
   => ( ~ v5_orders_3(sK7,sK4,sK5)
      & v5_orders_3(sK6,sK2,sK3)
      & sK6 = sK7
      & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))
      & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))
      & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

% (438)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_orders_3(X5,X2,X3)
                          & v5_orders_3(X4,X0,X1)
                          & X4 = X5
                          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & l1_orders_2(X3) )
              & l1_orders_2(X2) )
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( l1_orders_2(X2)
               => ! [X3] :
                    ( l1_orders_2(X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ! [X2] :
                ( ( l1_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( l1_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(X5) )
                           => ( ( v5_orders_3(X4,X0,X1)
                                & X4 = X5
                                & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                             => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( l1_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & v1_funct_1(X5) )
                         => ( ( v5_orders_3(X4,X0,X1)
                              & X4 = X5
                              & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
                              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                           => v5_orders_3(X5,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_9)).

fof(f49,plain,(
    ~ v5_orders_3(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | v5_orders_3(sK6,sK4,sK5) ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v5_orders_3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_orders_3(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_orders_3(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_orders_3(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ v5_orders_3(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X2,X1] :
      ( ( v5_orders_3(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    sP1(sK4,sK6,sK5) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f37,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,
    ( sP1(sK4,sK6,sK5)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,
    ( sP1(sK4,sK6,sK5)
    | ~ l1_orders_2(sK5)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f39,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,
    ( sP1(sK4,sK6,sK5)
    | ~ v1_funct_1(sK6)
    | ~ l1_orders_2(sK5)
    | ~ l1_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f85,f75])).

fof(f75,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f43,f47])).

fof(f43,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,
    ( sP1(sK4,sK6,sK5)
    | ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ v1_funct_1(sK6)
    | ~ l1_orders_2(sK5)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f84,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X0,X2,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f14,f17,f16])).

fof(f16,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( r1_orders_2(X1,X5,X6)
                      | k1_funct_1(X2,X4) != X6
                      | k1_funct_1(X2,X3) != X5
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r1_orders_2(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ! [X5] :
                            ( ! [X6] :
                                ( r1_orders_2(X1,X5,X6)
                                | k1_funct_1(X2,X4) != X6
                                | k1_funct_1(X2,X3) != X5
                                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        | ~ r1_orders_2(X0,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_orders_3(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_orders_2(X0,X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X1))
                                 => ( ( k1_funct_1(X2,X4) = X6
                                      & k1_funct_1(X2,X3) = X5 )
                                   => r1_orders_2(X1,X5,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).

fof(f84,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(forward_demodulation,[],[f44,f47])).

fof(f44,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f682,plain,
    ( sP0(sK5,sK6,sK4)
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(resolution,[],[f668,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2))
          & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2)
          & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
          & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2))
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( ! [X10] :
                        ( r1_orders_2(X0,X9,X10)
                        | k1_funct_1(X1,X8) != X10
                        | k1_funct_1(X1,X7) != X9
                        | ~ m1_subset_1(X10,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                | ~ r1_orders_2(X2,X7,X8)
                | ~ m1_subset_1(X8,u1_struct_0(X2)) )
            | ~ m1_subset_1(X7,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f33,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_orders_2(X0,X5,X6)
                      & k1_funct_1(X1,X4) = X6
                      & k1_funct_1(X1,X3) = X5
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_orders_2(X2,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X2)) )
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_orders_2(X0,X5,X6)
                    & k1_funct_1(X1,X4) = X6
                    & k1_funct_1(X1,sK8(X0,X1,X2)) = X5
                    & m1_subset_1(X6,u1_struct_0(X0)) )
                & m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_orders_2(X2,sK8(X0,X1,X2),X4)
            & m1_subset_1(X4,u1_struct_0(X2)) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_orders_2(X0,X5,X6)
                  & k1_funct_1(X1,X4) = X6
                  & k1_funct_1(X1,sK8(X0,X1,X2)) = X5
                  & m1_subset_1(X6,u1_struct_0(X0)) )
              & m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_orders_2(X2,sK8(X0,X1,X2),X4)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_orders_2(X0,X5,X6)
                & k1_funct_1(X1,sK9(X0,X1,X2)) = X6
                & k1_funct_1(X1,sK8(X0,X1,X2)) = X5
                & m1_subset_1(X6,u1_struct_0(X0)) )
            & m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_orders_2(X0,X5,X6)
              & k1_funct_1(X1,sK9(X0,X1,X2)) = X6
              & k1_funct_1(X1,sK8(X0,X1,X2)) = X5
              & m1_subset_1(X6,u1_struct_0(X0)) )
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ? [X6] :
            ( ~ r1_orders_2(X0,sK10(X0,X1,X2),X6)
            & k1_funct_1(X1,sK9(X0,X1,X2)) = X6
            & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)
            & m1_subset_1(X6,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( ~ r1_orders_2(X0,sK10(X0,X1,X2),X6)
          & k1_funct_1(X1,sK9(X0,X1,X2)) = X6
          & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2))
        & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2)
        & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X0,X5,X6)
                        & k1_funct_1(X1,X4) = X6
                        & k1_funct_1(X1,X3) = X5
                        & m1_subset_1(X6,u1_struct_0(X0)) )
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_orders_2(X2,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X2)) )
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( ! [X10] :
                        ( r1_orders_2(X0,X9,X10)
                        | k1_funct_1(X1,X8) != X10
                        | k1_funct_1(X1,X7) != X9
                        | ~ m1_subset_1(X10,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                | ~ r1_orders_2(X2,X7,X8)
                | ~ m1_subset_1(X8,u1_struct_0(X2)) )
            | ~ m1_subset_1(X7,u1_struct_0(X2)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_orders_2(X1,X5,X6)
                        & k1_funct_1(X2,X4) = X6
                        & k1_funct_1(X2,X3) = X5
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & r1_orders_2(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( ! [X6] :
                        ( r1_orders_2(X1,X5,X6)
                        | k1_funct_1(X2,X4) != X6
                        | k1_funct_1(X2,X3) != X5
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f668,plain,
    ( r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f667,f301])).

fof(f301,plain,
    ( m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ spl12_5 ),
    inference(backward_demodulation,[],[f97,f298])).

fof(f298,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK5)
    | ~ spl12_5 ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,
    ( ! [X14,X15] :
        ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK5) = X14 )
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl12_5
  <=> ! [X15,X14] :
        ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK5) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f97,plain,(
    m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f667,plain,
    ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f666,f300])).

fof(f300,plain,
    ( m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ spl12_5 ),
    inference(backward_demodulation,[],[f96,f298])).

fof(f96,plain,(
    m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f666,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(resolution,[],[f665,f595])).

fof(f595,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK5,X1,X0) )
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f589,f36])).

fof(f36,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f589,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X1,X0)
        | r1_orders_2(sK5,X1,X0)
        | ~ l1_orders_2(sK3) )
    | ~ spl12_5 ),
    inference(duplicate_literal_removal,[],[f588])).

fof(f588,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r1_orders_2(sK5,X1,X0)
        | ~ l1_orders_2(sK3) )
    | ~ spl12_5 ),
    inference(equality_resolution,[],[f431])).

fof(f431,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK5,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f430,f298])).

fof(f430,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK5,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl12_5 ),
    inference(forward_demodulation,[],[f132,f298])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK5,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f124,f38])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK5,X1,X2)
      | ~ l1_orders_2(sK5)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f70,f46])).

fof(f46,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

% (445)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (433)Refutation not found, incomplete strategy% (433)------------------------------
% (433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (433)Termination reason: Refutation not found, incomplete strategy

% (433)Memory used [KB]: 1791
% (433)Time elapsed: 0.134 s
% (433)------------------------------
% (433)------------------------------
fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f665,plain,
    ( r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f664,f83])).

fof(f83,plain,(
    sP0(sK3,sK6,sK2) ),
    inference(subsumption_resolution,[],[f81,f48])).

fof(f48,plain,(
    v5_orders_3(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,
    ( ~ v5_orders_3(sK6,sK2,sK3)
    | sP0(sK3,sK6,sK2) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v5_orders_3(X1,X0,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    sP1(sK2,sK6,sK3) ),
    inference(subsumption_resolution,[],[f79,f35])).

fof(f35,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f78,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ v1_funct_1(sK6)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f40,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_orders_2(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f41,f64])).

fof(f41,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f664,plain,
    ( r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ sP0(sK3,sK6,sK2)
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f661,f300])).

fof(f661,plain,
    ( r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ sP0(sK3,sK6,sK2)
    | ~ spl12_2
    | ~ spl12_5 ),
    inference(resolution,[],[f657,f301])).

fof(f657,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1))
        | r1_orders_2(X1,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
        | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X1))
        | ~ sP0(X1,sK6,sK2) )
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f656,f98])).

fof(f98,plain,(
    sK10(sK5,sK6,sK4) = k1_funct_1(sK6,sK8(sK5,sK6,sK4)) ),
    inference(resolution,[],[f92,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f656,plain,
    ( ! [X1] :
        ( r1_orders_2(X1,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
        | ~ m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1))
        | ~ sP0(X1,sK6,sK2) )
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f655,f98])).

fof(f655,plain,
    ( ! [X1] :
        ( r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4))
        | ~ m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1))
        | ~ sP0(X1,sK6,sK2) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f654,f201])).

fof(f201,plain,
    ( m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f93,f188])).

fof(f188,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK4)
    | ~ spl12_2 ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,
    ( ! [X14,X15] :
        ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK4) = X14 )
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl12_2
  <=> ! [X15,X14] :
        ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK4) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f93,plain,(
    m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK4)) ),
    inference(resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f654,plain,
    ( ! [X1] :
        ( r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4))
        | ~ m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1))
        | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
        | ~ sP0(X1,sK6,sK2) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f647,f202])).

fof(f202,plain,
    ( m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f94,f188])).

fof(f94,plain,(
    m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK4)) ),
    inference(resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f647,plain,
    ( ! [X1] :
        ( r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4))
        | ~ m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1))
        | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1))
        | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
        | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
        | ~ sP0(X1,sK6,sK2) )
    | ~ spl12_2 ),
    inference(resolution,[],[f373,f555])).

fof(f555,plain,
    ( r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f554,f202])).

fof(f554,plain,
    ( ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f551,f201])).

fof(f551,plain,
    ( ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4))
    | ~ spl12_2 ),
    inference(resolution,[],[f550,f95])).

fof(f95,plain,(
    r1_orders_2(sK4,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4)) ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f550,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK4,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X0) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f544,f35])).

fof(f544,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK4,X1,X0)
        | r1_orders_2(sK2,X1,X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl12_2 ),
    inference(duplicate_literal_removal,[],[f543])).

fof(f543,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK4,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl12_2 ),
    inference(equality_resolution,[],[f420])).

fof(f420,plain,
    ( ! [X4,X5,X3] :
        ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | ~ r1_orders_2(sK4,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | r1_orders_2(X3,X4,X5)
        | ~ l1_orders_2(X3) )
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f419,f188])).

fof(f419,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK2))
        | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
        | ~ r1_orders_2(sK4,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_subset_1(X4,u1_struct_0(sK4))
        | r1_orders_2(X3,X4,X5)
        | ~ l1_orders_2(X3) )
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f109,f188])).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_orders_2(sK4,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | r1_orders_2(X3,X4,X5)
      | ~ l1_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ r1_orders_2(sK4,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | r1_orders_2(X3,X4,X5)
      | ~ l1_orders_2(X3)
      | ~ l1_orders_2(sK4) ) ),
    inference(superposition,[],[f70,f45])).

fof(f45,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f373,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X2,X1,sK9(sK5,sK6,sK4))
      | r1_orders_2(X0,k1_funct_1(sK6,X1),sK11(sK5,sK6,sK4))
      | ~ m1_subset_1(k1_funct_1(sK6,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ sP0(X0,sK6,X2) ) ),
    inference(superposition,[],[f72,f99])).

fof(f99,plain,(
    sK11(sK5,sK6,sK4) = k1_funct_1(sK6,sK9(sK5,sK6,sK4)) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8))
      | ~ m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r1_orders_2(X0,X9,k1_funct_1(X1,X8))
      | k1_funct_1(X1,X7) != X9
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X10,X8,X7,X1,X9] :
      ( r1_orders_2(X0,X9,X10)
      | k1_funct_1(X1,X8) != X10
      | k1_funct_1(X1,X7) != X9
      | ~ m1_subset_1(X10,u1_struct_0(X0))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f169,plain,(
    spl12_4 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl12_4 ),
    inference(subsumption_resolution,[],[f167,f38])).

fof(f167,plain,
    ( ~ l1_orders_2(sK5)
    | spl12_4 ),
    inference(resolution,[],[f139,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f139,plain,
    ( ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl12_4
  <=> m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f150,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f148,f37])).

fof(f148,plain,
    ( ~ l1_orders_2(sK4)
    | spl12_1 ),
    inference(resolution,[],[f115,f50])).

fof(f115,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl12_1
  <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f143,plain,
    ( ~ spl12_4
    | spl12_5 ),
    inference(avatar_split_clause,[],[f129,f141,f137])).

fof(f129,plain,(
    ! [X14,X15] :
      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15)
      | u1_struct_0(sK5) = X14
      | ~ m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ) ),
    inference(superposition,[],[f65,f46])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f119,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f105,f117,f113])).

fof(f105,plain,(
    ! [X14,X15] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15)
      | u1_struct_0(sK4) = X14
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f65,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:27:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (426)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (429)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (437)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (431)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (430)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (444)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (428)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (448)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (426)Refutation not found, incomplete strategy% (426)------------------------------
% 0.21/0.51  % (426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (446)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (439)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (433)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (442)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (435)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (449)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (426)Memory used [KB]: 10618
% 0.21/0.52  % (426)Time elapsed: 0.097 s
% 0.21/0.52  % (426)------------------------------
% 0.21/0.52  % (426)------------------------------
% 0.21/0.52  % (450)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (427)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (436)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (440)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (432)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (441)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (434)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (447)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (451)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (443)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (439)Refutation not found, incomplete strategy% (439)------------------------------
% 0.21/0.54  % (439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (439)Memory used [KB]: 6268
% 0.21/0.54  % (439)Time elapsed: 0.113 s
% 0.21/0.54  % (439)------------------------------
% 0.21/0.54  % (439)------------------------------
% 0.21/0.54  % (437)Refutation not found, incomplete strategy% (437)------------------------------
% 0.21/0.54  % (437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (437)Memory used [KB]: 10618
% 0.21/0.54  % (437)Time elapsed: 0.117 s
% 0.21/0.54  % (437)------------------------------
% 0.21/0.54  % (437)------------------------------
% 0.21/0.54  % (432)Refutation not found, incomplete strategy% (432)------------------------------
% 0.21/0.54  % (432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (432)Memory used [KB]: 10618
% 0.21/0.54  % (432)Time elapsed: 0.084 s
% 0.21/0.54  % (432)------------------------------
% 0.21/0.54  % (432)------------------------------
% 0.21/0.54  % (427)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f685,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f119,f143,f150,f169,f684])).
% 0.21/0.54  fof(f684,plain,(
% 0.21/0.54    ~spl12_2 | ~spl12_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f683])).
% 0.21/0.54  fof(f683,plain,(
% 0.21/0.54    $false | (~spl12_2 | ~spl12_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f682,f92])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ~sP0(sK5,sK6,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f91,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ~v5_orders_3(sK6,sK4,sK5)),
% 0.21/0.54    inference(forward_demodulation,[],[f49,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    sK6 = sK7),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    (((((~v5_orders_3(sK7,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = sK7 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & l1_orders_2(sK5)) & l1_orders_2(sK4)) & l1_orders_2(sK3)) & l1_orders_2(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f9,f24,f23,f22,f21,f20,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) => (~v5_orders_3(sK7,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = sK7 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK7))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (438)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.54  fof(f6,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f5])).
% 0.21/0.54  fof(f5,conjecture,(
% 0.21/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_9)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ~v5_orders_3(sK7,sK4,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ~sP0(sK5,sK6,sK4) | v5_orders_3(sK6,sK4,sK5)),
% 0.21/0.54    inference(resolution,[],[f89,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | v5_orders_3(X1,X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v5_orders_3(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~v5_orders_3(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v5_orders_3(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    sP1(sK4,sK6,sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f88,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    l1_orders_2(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    sP1(sK4,sK6,sK5) | ~l1_orders_2(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f87,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    l1_orders_2(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    sP1(sK4,sK6,sK5) | ~l1_orders_2(sK5) | ~l1_orders_2(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    v1_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    sP1(sK4,sK6,sK5) | ~v1_funct_1(sK6) | ~l1_orders_2(sK5) | ~l1_orders_2(sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5))),
% 0.21/0.54    inference(forward_demodulation,[],[f43,f47])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    sP1(sK4,sK6,sK5) | ~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK5)) | ~v1_funct_1(sK6) | ~l1_orders_2(sK5) | ~l1_orders_2(sK4)),
% 0.21/0.54    inference(resolution,[],[f84,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP1(X0,X2,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(definition_folding,[],[f14,f17,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 0.21/0.54    inference(forward_demodulation,[],[f44,f47])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5))))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f682,plain,(
% 0.21/0.54    sP0(sK5,sK6,sK4) | (~spl12_2 | ~spl12_5)),
% 0.21/0.54    inference(resolution,[],[f668,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f29,f33,f32,f31,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) => (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (~r1_orders_2(X0,sK10(X0,X1,X2),X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X0,sK10(X0,X1,X2),X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) => (~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X2,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f16])).
% 0.21/0.54  fof(f668,plain,(
% 0.21/0.54    r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | (~spl12_2 | ~spl12_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f667,f301])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~spl12_5),
% 0.21/0.54    inference(backward_demodulation,[],[f97,f298])).
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    u1_struct_0(sK3) = u1_struct_0(sK5) | ~spl12_5),
% 0.21/0.54    inference(equality_resolution,[],[f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X14,X15] : (g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15) | u1_struct_0(sK5) = X14) ) | ~spl12_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f141])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl12_5 <=> ! [X15,X14] : (g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15) | u1_struct_0(sK5) = X14)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.21/0.54    inference(resolution,[],[f92,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f667,plain,(
% 0.21/0.54    ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | (~spl12_2 | ~spl12_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f666,f300])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~spl12_5),
% 0.21/0.54    inference(backward_demodulation,[],[f96,f298])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.21/0.54    inference(resolution,[],[f92,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f666,plain,(
% 0.21/0.54    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | r1_orders_2(sK5,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | (~spl12_2 | ~spl12_5)),
% 0.21/0.54    inference(resolution,[],[f665,f595])).
% 0.21/0.54  fof(f595,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_orders_2(sK3,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_orders_2(sK5,X1,X0)) ) | ~spl12_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f589,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    l1_orders_2(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f589,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X1,X0) | r1_orders_2(sK5,X1,X0) | ~l1_orders_2(sK3)) ) | ~spl12_5),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f588])).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | r1_orders_2(sK5,X1,X0) | ~l1_orders_2(sK3)) ) | ~spl12_5),
% 0.21/0.54    inference(equality_resolution,[],[f431])).
% 0.21/0.54  fof(f431,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(sK5,X1,X2) | ~l1_orders_2(X0)) ) | ~spl12_5),
% 0.21/0.54    inference(forward_demodulation,[],[f430,f298])).
% 0.21/0.54  fof(f430,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK3)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(sK5,X1,X2) | ~l1_orders_2(X0)) ) | ~spl12_5),
% 0.21/0.54    inference(forward_demodulation,[],[f132,f298])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(sK5,X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f38])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(sK5,X1,X2) | ~l1_orders_2(sK5) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(superposition,[],[f70,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X4,X0,X5,X1] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~r1_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X1,X4,X5) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X5) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_orders_2(X1,X4,X5) | ~r2_orders_2(X0,X2,X3)) & (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3))) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  % (445)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (433)Refutation not found, incomplete strategy% (433)------------------------------
% 0.21/0.55  % (433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (433)Memory used [KB]: 1791
% 0.21/0.55  % (433)Time elapsed: 0.134 s
% 0.21/0.55  % (433)------------------------------
% 0.21/0.55  % (433)------------------------------
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_orders_2(X1,X4,X5) | ~r2_orders_2(X0,X2,X3)) & (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3))) | (X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).
% 0.21/0.56  fof(f665,plain,(
% 0.21/0.56    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | (~spl12_2 | ~spl12_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f664,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    sP0(sK3,sK6,sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f81,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    v5_orders_3(sK6,sK2,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ~v5_orders_3(sK6,sK2,sK3) | sP0(sK3,sK6,sK2)),
% 0.21/0.56    inference(resolution,[],[f80,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v5_orders_3(X1,X0,X2) | sP0(X2,X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    sP1(sK2,sK6,sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f79,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    l1_orders_2(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    sP1(sK2,sK6,sK3) | ~l1_orders_2(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    sP1(sK2,sK6,sK3) | ~l1_orders_2(sK3) | ~l1_orders_2(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f77,f39])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    sP1(sK2,sK6,sK3) | ~v1_funct_1(sK6) | ~l1_orders_2(sK3) | ~l1_orders_2(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f76,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    sP1(sK2,sK6,sK3) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_orders_2(sK3) | ~l1_orders_2(sK2)),
% 0.21/0.56    inference(resolution,[],[f41,f64])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f664,plain,(
% 0.21/0.56    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~sP0(sK3,sK6,sK2) | (~spl12_2 | ~spl12_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f661,f300])).
% 0.21/0.56  fof(f661,plain,(
% 0.21/0.56    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~sP0(sK3,sK6,sK2) | (~spl12_2 | ~spl12_5)),
% 0.21/0.56    inference(resolution,[],[f657,f301])).
% 0.21/0.56  fof(f657,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1)) | r1_orders_2(X1,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X1)) | ~sP0(X1,sK6,sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(forward_demodulation,[],[f656,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    sK10(sK5,sK6,sK4) = k1_funct_1(sK6,sK8(sK5,sK6,sK4))),
% 0.21/0.56    inference(resolution,[],[f92,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f656,plain,(
% 0.21/0.56    ( ! [X1] : (r1_orders_2(X1,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1)) | ~sP0(X1,sK6,sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(forward_demodulation,[],[f655,f98])).
% 0.21/0.56  fof(f655,plain,(
% 0.21/0.56    ( ! [X1] : (r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4)) | ~m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1)) | ~sP0(X1,sK6,sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f654,f201])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~spl12_2),
% 0.21/0.56    inference(backward_demodulation,[],[f93,f188])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    u1_struct_0(sK2) = u1_struct_0(sK4) | ~spl12_2),
% 0.21/0.56    inference(equality_resolution,[],[f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X14,X15] : (g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15) | u1_struct_0(sK4) = X14) ) | ~spl12_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl12_2 <=> ! [X15,X14] : (g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15) | u1_struct_0(sK4) = X14)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK4))),
% 0.21/0.56    inference(resolution,[],[f92,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f654,plain,(
% 0.21/0.56    ( ! [X1] : (r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4)) | ~m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~sP0(X1,sK6,sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f647,f202])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~spl12_2),
% 0.21/0.56    inference(backward_demodulation,[],[f94,f188])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK4))),
% 0.21/0.56    inference(resolution,[],[f92,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f647,plain,(
% 0.21/0.56    ( ! [X1] : (r1_orders_2(X1,k1_funct_1(sK6,sK8(sK5,sK6,sK4)),sK11(sK5,sK6,sK4)) | ~m1_subset_1(k1_funct_1(sK6,sK8(sK5,sK6,sK4)),u1_struct_0(X1)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~sP0(X1,sK6,sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(resolution,[],[f373,f555])).
% 0.21/0.56  fof(f555,plain,(
% 0.21/0.56    r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4)) | ~spl12_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f554,f202])).
% 0.21/0.56  fof(f554,plain,(
% 0.21/0.56    ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4)) | ~spl12_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f551,f201])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK2,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4)) | ~spl12_2),
% 0.21/0.56    inference(resolution,[],[f550,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    r1_orders_2(sK4,sK8(sK5,sK6,sK4),sK9(sK5,sK6,sK4))),
% 0.21/0.56    inference(resolution,[],[f92,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f550,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_orders_2(sK4,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X0)) ) | ~spl12_2),
% 0.21/0.56    inference(subsumption_resolution,[],[f544,f35])).
% 0.21/0.56  fof(f544,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK4,X1,X0) | r1_orders_2(sK2,X1,X0) | ~l1_orders_2(sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f543])).
% 0.21/0.56  fof(f543,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK4,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X0) | ~l1_orders_2(sK2)) ) | ~spl12_2),
% 0.21/0.56    inference(equality_resolution,[],[f420])).
% 0.21/0.56  fof(f420,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~m1_subset_1(X5,u1_struct_0(sK2)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | ~r1_orders_2(sK4,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | r1_orders_2(X3,X4,X5) | ~l1_orders_2(X3)) ) | ~spl12_2),
% 0.21/0.56    inference(forward_demodulation,[],[f419,f188])).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,u1_struct_0(sK2)) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~r1_orders_2(sK4,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_orders_2(X3,X4,X5) | ~l1_orders_2(X3)) ) | ~spl12_2),
% 0.21/0.56    inference(forward_demodulation,[],[f109,f188])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~r1_orders_2(sK4,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_orders_2(X3,X4,X5) | ~l1_orders_2(X3)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f101,f37])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~r1_orders_2(sK4,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(sK4)) | ~m1_subset_1(X4,u1_struct_0(sK4)) | r1_orders_2(X3,X4,X5) | ~l1_orders_2(X3) | ~l1_orders_2(sK4)) )),
% 0.21/0.56    inference(superposition,[],[f70,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f373,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X2,X1,sK9(sK5,sK6,sK4)) | r1_orders_2(X0,k1_funct_1(sK6,X1),sK11(sK5,sK6,sK4)) | ~m1_subset_1(k1_funct_1(sK6,X1),u1_struct_0(X0)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~sP0(X0,sK6,X2)) )),
% 0.21/0.56    inference(superposition,[],[f72,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    sK11(sK5,sK6,sK4) = k1_funct_1(sK6,sK9(sK5,sK6,sK4))),
% 0.21/0.56    inference(resolution,[],[f92,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X8,X7,X1] : (~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8)) | ~m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X0,X9,k1_funct_1(X1,X8)) | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    spl12_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    $false | spl12_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f167,f38])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    ~l1_orders_2(sK5) | spl12_4),
% 0.21/0.56    inference(resolution,[],[f139,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    ~m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) | spl12_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f137])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    spl12_4 <=> m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    spl12_1),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    $false | spl12_1),
% 0.21/0.56    inference(subsumption_resolution,[],[f148,f37])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ~l1_orders_2(sK4) | spl12_1),
% 0.21/0.56    inference(resolution,[],[f115,f50])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ~m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) | spl12_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f113])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    spl12_1 <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ~spl12_4 | spl12_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f129,f141,f137])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ( ! [X14,X15] : (g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X14,X15) | u1_struct_0(sK5) = X14 | ~m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))) )),
% 0.21/0.56    inference(superposition,[],[f65,f46])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    ~spl12_1 | spl12_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f105,f117,f113])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X14,X15] : (g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != g1_orders_2(X14,X15) | u1_struct_0(sK4) = X14 | ~m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))) )),
% 0.21/0.56    inference(superposition,[],[f65,f45])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (427)------------------------------
% 0.21/0.56  % (427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (427)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (427)Memory used [KB]: 11129
% 0.21/0.56  % (427)Time elapsed: 0.118 s
% 0.21/0.56  % (427)------------------------------
% 0.21/0.56  % (427)------------------------------
% 1.53/0.56  % (425)Success in time 0.19 s
%------------------------------------------------------------------------------
