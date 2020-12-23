%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  161 (6146 expanded)
%              Number of leaves         :   18 (2799 expanded)
%              Depth                    :   57
%              Number of atoms          :  890 (89730 expanded)
%              Number of equality atoms :  187 (20866 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f397,plain,(
    $false ),
    inference(subsumption_resolution,[],[f396,f267])).

fof(f267,plain,(
    ~ sP0(sK5,sK6,sK4) ),
    inference(subsumption_resolution,[],[f265,f73])).

fof(f73,plain,(
    ~ v5_orders_3(sK6,sK4,sK5) ),
    inference(backward_demodulation,[],[f51,f49])).

fof(f49,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f26,f25,f24,f23,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f51,plain,(
    ~ v5_orders_3(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f265,plain,
    ( ~ sP0(sK5,sK6,sK4)
    | v5_orders_3(sK6,sK4,sK5) ),
    inference(resolution,[],[f262,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v5_orders_3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_orders_3(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_orders_3(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( ( v5_orders_3(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ v5_orders_3(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X2,X1] :
      ( ( v5_orders_3(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f262,plain,(
    sP1(sK4,sK6,sK5) ),
    inference(subsumption_resolution,[],[f261,f40])).

fof(f40,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f261,plain,
    ( sP1(sK4,sK6,sK5)
    | ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f260,f43])).

fof(f43,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f260,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP1(sK4,sK6,sK5)
    | ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f256,f42])).

fof(f42,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f256,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | sP1(sK4,sK6,sK5)
    | ~ l1_orders_2(sK5) ),
    inference(superposition,[],[f226,f122])).

fof(f122,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f119,f78])).

fof(f78,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = k7_lattice3(k7_lattice3(sK3)) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).

fof(f119,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK3))
    | u1_struct_0(sK3) = u1_struct_0(sK5) ),
    inference(superposition,[],[f87,f82])).

fof(f82,plain,(
    g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = k7_lattice3(k7_lattice3(sK3)) ),
    inference(backward_demodulation,[],[f48,f78])).

fof(f48,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_struct_0(sK3) = X2 ) ),
    inference(resolution,[],[f85,f38])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f226,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X2))
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2))))
      | sP1(sK4,sK6,X2)
      | ~ l1_orders_2(X2) ) ),
    inference(forward_demodulation,[],[f225,f97])).

fof(f97,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f92,f77])).

fof(f77,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | u1_struct_0(sK2) = u1_struct_0(sK4) ),
    inference(superposition,[],[f86,f81])).

fof(f81,plain,(
    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = k7_lattice3(k7_lattice3(sK2)) ),
    inference(backward_demodulation,[],[f47,f77])).

fof(f47,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(resolution,[],[f85,f37])).

fof(f225,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X2))
      | sP1(sK4,sK6,X2)
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2)))) ) ),
    inference(forward_demodulation,[],[f223,f97])).

fof(f223,plain,(
    ! [X2] :
      ( ~ v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(X2))
      | sP1(sK4,sK6,X2)
      | ~ l1_orders_2(X2)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2)))) ) ),
    inference(resolution,[],[f182,f39])).

fof(f39,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
      | sP1(X0,sK6,X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    v1_funct_1(sK6) ),
    inference(forward_demodulation,[],[f44,f49])).

fof(f44,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | sP1(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f19,f18])).

fof(f18,plain,(
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f396,plain,(
    sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f395,f130])).

fof(f130,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK10(sK5,X2,X3),u1_struct_0(sK3))
      | sP0(sK5,X2,X3) ) ),
    inference(superposition,[],[f61,f122])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f31,f35,f34,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
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

fof(f34,plain,(
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

fof(f35,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f395,plain,(
    ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f394,f267])).

fof(f394,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f390,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(sK5,X0,X1),u1_struct_0(sK3))
      | sP0(sK5,X0,X1) ) ),
    inference(superposition,[],[f62,f122])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f390,plain,
    ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f389,f122])).

fof(f389,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f388,f78])).

fof(f388,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f387,f122])).

fof(f387,plain,
    ( k7_lattice3(k7_lattice3(sK3)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f386,f189])).

fof(f189,plain,(
    u1_orders_2(sK3) = u1_orders_2(sK5) ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k7_lattice3(k7_lattice3(sK3)) != k7_lattice3(k7_lattice3(sK3))
    | u1_orders_2(sK3) = u1_orders_2(sK5) ),
    inference(superposition,[],[f184,f78])).

fof(f184,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK3))
      | u1_orders_2(sK5) = X1 ) ),
    inference(superposition,[],[f138,f127])).

fof(f127,plain,(
    k7_lattice3(k7_lattice3(sK3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK5)) ),
    inference(backward_demodulation,[],[f82,f122])).

fof(f138,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK5))
      | u1_orders_2(sK5) = X1 ) ),
    inference(resolution,[],[f134,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f134,plain,(
    m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f133,plain,
    ( m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK5) ),
    inference(superposition,[],[f53,f122])).

fof(f386,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f385,f122])).

fof(f385,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f384,f267])).

fof(f384,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))
    | sP0(sK5,sK6,sK4) ),
    inference(subsumption_resolution,[],[f379,f40])).

fof(f379,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5))
    | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))
    | ~ l1_orders_2(sK5)
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f378,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f378,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f377,f267])).

fof(f377,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | ~ l1_orders_2(X0)
      | sP0(sK5,sK6,sK4) ) ),
    inference(resolution,[],[f376,f130])).

fof(f376,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f375,f267])).

fof(f375,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ l1_orders_2(X0)
      | sP0(sK5,sK6,sK4) ) ),
    inference(resolution,[],[f374,f129])).

fof(f374,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ l1_orders_2(X0) ) ),
    inference(forward_demodulation,[],[f373,f78])).

fof(f373,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f371,f38])).

fof(f371,plain,(
    ! [X0] :
      ( r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK3) ) ),
    inference(resolution,[],[f370,f70])).

fof(f70,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r1_orders_2(X0,X2,X3)
                          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r1_orders_2(X0,X2,X3)
                          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X0,X2,X3)
                              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_yellow_6)).

fof(f370,plain,(
    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f369,f267])).

fof(f369,plain,
    ( r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f368,f107])).

fof(f107,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK8(X6,X7,sK4),u1_struct_0(sK2))
      | sP0(X6,X7,sK4) ) ),
    inference(superposition,[],[f58,f97])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f368,plain,
    ( ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f367,f267])).

fof(f367,plain,
    ( ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f366,f106])).

fof(f106,plain,(
    ! [X4,X5] :
      ( m1_subset_1(sK9(X4,X5,sK4),u1_struct_0(sK2))
      | sP0(X4,X5,sK4) ) ),
    inference(superposition,[],[f59,f97])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f366,plain,
    ( ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f365,f267])).

fof(f365,plain,
    ( ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f364,f130])).

fof(f364,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f363,f267])).

fof(f363,plain,
    ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))
    | sP0(sK5,sK6,sK4) ),
    inference(resolution,[],[f362,f129])).

fof(f362,plain,
    ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f361,f37])).

fof(f361,plain,
    ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f360,f77])).

fof(f360,plain,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))
    | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ),
    inference(resolution,[],[f357,f240])).

fof(f240,plain,(
    sP0(sK3,sK6,sK2) ),
    inference(subsumption_resolution,[],[f239,f50])).

fof(f50,plain,(
    v5_orders_3(sK6,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f239,plain,
    ( ~ v5_orders_3(sK6,sK2,sK3)
    | sP0(sK3,sK6,sK2) ),
    inference(resolution,[],[f233,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v5_orders_3(X1,X0,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f233,plain,(
    sP1(sK2,sK6,sK3) ),
    inference(subsumption_resolution,[],[f232,f43])).

fof(f232,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subsumption_resolution,[],[f229,f38])).

fof(f229,plain,
    ( sP1(sK2,sK6,sK3)
    | ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(resolution,[],[f221,f42])).

fof(f221,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X0))
      | sP1(sK2,sK6,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f182,f37])).

fof(f357,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,sK6,X1)
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(sK2))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) ) ),
    inference(forward_demodulation,[],[f356,f268])).

fof(f268,plain,(
    k1_funct_1(sK6,sK9(sK5,sK6,sK4)) = sK11(sK5,sK6,sK4) ),
    inference(resolution,[],[f267,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f356,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(sK2))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(forward_demodulation,[],[f355,f77])).

fof(f355,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(forward_demodulation,[],[f354,f97])).

fof(f354,plain,(
    ! [X0,X1] :
      ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK2))
      | ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(forward_demodulation,[],[f353,f163])).

fof(f163,plain,(
    u1_orders_2(sK2) = u1_orders_2(sK4) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( k7_lattice3(k7_lattice3(sK2)) != k7_lattice3(k7_lattice3(sK2))
    | u1_orders_2(sK2) = u1_orders_2(sK4) ),
    inference(superposition,[],[f152,f77])).

fof(f152,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK2))
      | u1_orders_2(sK4) = X1 ) ),
    inference(superposition,[],[f117,f99])).

fof(f99,plain,(
    k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK4)) ),
    inference(backward_demodulation,[],[f81,f97])).

fof(f117,plain,(
    ! [X4,X3] :
      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK4)) != g1_orders_2(X3,X4)
      | u1_orders_2(sK4) = X4 ) ),
    inference(resolution,[],[f68,f109])).

fof(f109,plain,(
    m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f108,f39])).

fof(f108,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK4) ),
    inference(superposition,[],[f53,f97])).

fof(f353,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(forward_demodulation,[],[f352,f268])).

fof(f352,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(subsumption_resolution,[],[f351,f267])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | sP0(sK5,sK6,sK4)
      | ~ m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(subsumption_resolution,[],[f348,f39])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(sK4)
      | sP0(sK5,sK6,sK4)
      | ~ m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4)))
      | ~ sP0(X0,sK6,X1) ) ),
    inference(superposition,[],[f291,f269])).

fof(f269,plain,(
    k1_funct_1(sK6,sK8(sK5,sK6,sK4)) = sK10(sK5,sK6,sK4) ),
    inference(resolution,[],[f267,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f291,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( ~ m1_subset_1(k1_funct_1(X9,sK8(X7,X8,X6)),u1_struct_0(X10))
      | ~ m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5))
      | ~ m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X6)
      | sP0(X7,X8,X6)
      | ~ m1_subset_1(k1_funct_1(X9,sK9(X7,X8,X6)),u1_struct_0(X10))
      | g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | r1_orders_2(X10,k1_funct_1(X9,sK8(X7,X8,X6)),k1_funct_1(X9,sK9(X7,X8,X6)))
      | ~ sP0(X10,X9,X5) ) ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5))
      | ~ m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5))
      | ~ l1_orders_2(X5)
      | ~ l1_orders_2(X6)
      | sP0(X7,X8,X6)
      | ~ m1_subset_1(k1_funct_1(X9,sK9(X7,X8,X6)),u1_struct_0(X10))
      | ~ m1_subset_1(k1_funct_1(X9,sK8(X7,X8,X6)),u1_struct_0(X10))
      | r1_orders_2(X10,k1_funct_1(X9,sK8(X7,X8,X6)),k1_funct_1(X9,sK9(X7,X8,X6)))
      | ~ m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5))
      | ~ m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5))
      | ~ sP0(X10,X9,X5) ) ),
    inference(resolution,[],[f280,f72])).

fof(f72,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( ~ r1_orders_2(X2,X7,X8)
      | ~ m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0))
      | ~ m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0))
      | r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8))
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
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f280,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | ~ m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X3)
      | sP0(X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f279,f58])).

fof(f279,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | ~ m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X3))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X3)
      | sP0(X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f278,f59])).

fof(f278,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | ~ m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X3))
      | ~ m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X3))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X3)
      | sP0(X1,X2,X3) ) ),
    inference(resolution,[],[f70,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:43:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (7277)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (7285)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (7274)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (7285)Refutation not found, incomplete strategy% (7285)------------------------------
% 0.22/0.55  % (7285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7278)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (7280)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (7297)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  % (7285)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7285)Memory used [KB]: 10618
% 0.22/0.55  % (7285)Time elapsed: 0.110 s
% 0.22/0.55  % (7285)------------------------------
% 0.22/0.55  % (7285)------------------------------
% 0.22/0.55  % (7279)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (7280)Refutation not found, incomplete strategy% (7280)------------------------------
% 0.22/0.55  % (7280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7280)Memory used [KB]: 10618
% 0.22/0.55  % (7280)Time elapsed: 0.120 s
% 0.22/0.55  % (7280)------------------------------
% 0.22/0.55  % (7280)------------------------------
% 0.22/0.55  % (7281)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (7277)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f397,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f396,f267])).
% 0.22/0.55  fof(f267,plain,(
% 0.22/0.55    ~sP0(sK5,sK6,sK4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f265,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ~v5_orders_3(sK6,sK4,sK5)),
% 0.22/0.55    inference(backward_demodulation,[],[f51,f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    sK6 = sK7),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    (((((~v5_orders_3(sK7,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = sK7 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & l1_orders_2(sK5)) & l1_orders_2(sK4)) & l1_orders_2(sK3)) & l1_orders_2(sK2)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f26,f25,f24,f23,f22,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) => (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(sK4))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,X3) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(X3)) => (? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & l1_orders_2(sK5))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X4] : (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(X4,sK2,sK3) & X4 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ? [X5] : (~v5_orders_3(X5,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = X5 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(X5)) => (~v5_orders_3(sK7,sK4,sK5) & v5_orders_3(sK6,sK2,sK3) & sK6 = sK7 & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK5)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK5)) & v1_funct_1(sK7))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~v5_orders_3(X5,X2,X3) & v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.22/0.56    inference(flattening,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~v5_orders_3(X5,X2,X3) & (v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & l1_orders_2(X3)) & l1_orders_2(X2)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (l1_orders_2(X2) => ! [X3] : (l1_orders_2(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.56  fof(f7,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f6])).
% 0.22/0.56  fof(f6,conjecture,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((l1_orders_2(X2) & ~v2_struct_0(X2)) => ! [X3] : ((l1_orders_2(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => ((v5_orders_3(X4,X0,X1) & X4 = X5 & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) => v5_orders_3(X5,X2,X3))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_waybel_9)).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ~v5_orders_3(sK7,sK4,sK5)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f265,plain,(
% 0.22/0.56    ~sP0(sK5,sK6,sK4) | v5_orders_3(sK6,sK4,sK5)),
% 0.22/0.56    inference(resolution,[],[f262,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | v5_orders_3(X1,X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((v5_orders_3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~v5_orders_3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.56    inference(rectify,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X2,X1] : (((v5_orders_3(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~v5_orders_3(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X2,X1] : ((v5_orders_3(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    sP1(sK4,sK6,sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f261,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    l1_orders_2(sK5)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    sP1(sK4,sK6,sK5) | ~l1_orders_2(sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f260,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP1(sK4,sK6,sK5) | ~l1_orders_2(sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f256,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | sP1(sK4,sK6,sK5) | ~l1_orders_2(sK5)),
% 0.22/0.56    inference(superposition,[],[f226,f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    u1_struct_0(sK3) = u1_struct_0(sK5)),
% 0.22/0.56    inference(subsumption_resolution,[],[f119,f78])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = k7_lattice3(k7_lattice3(sK3))),
% 0.22/0.56    inference(resolution,[],[f52,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    l1_orders_2(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_orders_2(X0) | k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0] : (k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => k7_lattice3(k7_lattice3(X0)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_lattice3)).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK3)) | u1_struct_0(sK3) = u1_struct_0(sK5)),
% 0.22/0.56    inference(superposition,[],[f87,f82])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) = k7_lattice3(k7_lattice3(sK3))),
% 0.22/0.56    inference(backward_demodulation,[],[f48,f78])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5))),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X2,X3] : (g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_struct_0(sK3) = X2) )),
% 0.22/0.56    inference(resolution,[],[f85,f38])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)) )),
% 0.22/0.56    inference(resolution,[],[f67,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    ( ! [X2] : (~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X2)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X2)))) | sP1(sK4,sK6,X2) | ~l1_orders_2(X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f225,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    u1_struct_0(sK2) = u1_struct_0(sK4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f92,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = k7_lattice3(k7_lattice3(sK2))),
% 0.22/0.56    inference(resolution,[],[f52,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    l1_orders_2(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2)) | u1_struct_0(sK2) = u1_struct_0(sK4)),
% 0.22/0.56    inference(superposition,[],[f86,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) = k7_lattice3(k7_lattice3(sK2))),
% 0.22/0.56    inference(backward_demodulation,[],[f47,f77])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | u1_struct_0(sK2) = X0) )),
% 0.22/0.56    inference(resolution,[],[f85,f37])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    ( ! [X2] : (~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X2)) | sP1(sK4,sK6,X2) | ~l1_orders_2(X2) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2))))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f223,f97])).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    ( ! [X2] : (~v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(X2)) | sP1(sK4,sK6,X2) | ~l1_orders_2(X2) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X2))))) )),
% 0.22/0.56    inference(resolution,[],[f182,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    l1_orders_2(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) | sP1(X0,sK6,X1) | ~l1_orders_2(X1) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))) )),
% 0.22/0.56    inference(resolution,[],[f66,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    v1_funct_1(sK6)),
% 0.22/0.56    inference(forward_demodulation,[],[f44,f49])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    v1_funct_1(sK7)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(definition_folding,[],[f16,f19,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_orders_3(X2,X0,X1) <=> ! [X3] : (! [X4] : ((! [X5] : (! [X6] : ((r1_orders_2(X1,X5,X6) | (k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5)) | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_orders_3(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_orders_2(X0,X3,X4) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X1)) => ((k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5) => r1_orders_2(X1,X5,X6)))))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_3)).
% 0.22/0.56  fof(f396,plain,(
% 0.22/0.56    sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f395,f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ( ! [X2,X3] : (m1_subset_1(sK10(sK5,X2,X3),u1_struct_0(sK3)) | sP0(sK5,X2,X3)) )),
% 0.22/0.56    inference(superposition,[],[f61,f122])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f31,f35,f34,f33,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2))) => (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),X4) & m1_subset_1(X4,u1_struct_0(X2))) => (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) => (? [X6] : (~r1_orders_2(X0,sK10(X0,X1,X2),X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X6] : (~r1_orders_2(X0,sK10(X0,X1,X2),X6) & k1_funct_1(X1,sK9(X0,X1,X2)) = X6 & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(X6,u1_struct_0(X0))) => (~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) & k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2) & k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X0,X5,X6) & k1_funct_1(X1,X4) = X6 & k1_funct_1(X1,X3) = X5 & m1_subset_1(X6,u1_struct_0(X0))) & m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X2,X3,X4) & m1_subset_1(X4,u1_struct_0(X2))) & m1_subset_1(X3,u1_struct_0(X2)))) & (! [X7] : (! [X8] : (! [X9] : (! [X10] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0))) | ~m1_subset_1(X9,u1_struct_0(X0))) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X1,X5,X6) & k1_funct_1(X2,X4) = X6 & k1_funct_1(X2,X3) = X5 & m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_orders_2(X1,X5,X6) | k1_funct_1(X2,X4) != X6 | k1_funct_1(X2,X3) != X5 | ~m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r1_orders_2(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X2,X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f18])).
% 0.22/0.56  fof(f395,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))),
% 0.22/0.56    inference(subsumption_resolution,[],[f394,f267])).
% 0.22/0.56  fof(f394,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f390,f129])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(sK11(sK5,X0,X1),u1_struct_0(sK3)) | sP0(sK5,X0,X1)) )),
% 0.22/0.56    inference(superposition,[],[f62,f122])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X0)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f390,plain,(
% 0.22/0.56    ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3))),
% 0.22/0.56    inference(forward_demodulation,[],[f389,f122])).
% 0.22/0.56  fof(f389,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.22/0.56    inference(subsumption_resolution,[],[f388,f78])).
% 0.22/0.56  fof(f388,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.22/0.56    inference(forward_demodulation,[],[f387,f122])).
% 0.22/0.56  fof(f387,plain,(
% 0.22/0.56    k7_lattice3(k7_lattice3(sK3)) != g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.22/0.56    inference(forward_demodulation,[],[f386,f189])).
% 0.22/0.56  fof(f189,plain,(
% 0.22/0.56    u1_orders_2(sK3) = u1_orders_2(sK5)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f187])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    k7_lattice3(k7_lattice3(sK3)) != k7_lattice3(k7_lattice3(sK3)) | u1_orders_2(sK3) = u1_orders_2(sK5)),
% 0.22/0.56    inference(superposition,[],[f184,f78])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK3)) | u1_orders_2(sK5) = X1) )),
% 0.22/0.56    inference(superposition,[],[f138,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    k7_lattice3(k7_lattice3(sK3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK5))),
% 0.22/0.56    inference(backward_demodulation,[],[f82,f122])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK5)) | u1_orders_2(sK5) = X1) )),
% 0.22/0.56    inference(resolution,[],[f134,f68])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f133,f40])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    m1_subset_1(u1_orders_2(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) | ~l1_orders_2(sK5)),
% 0.22/0.56    inference(superposition,[],[f53,f122])).
% 0.22/0.56  fof(f386,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.22/0.56    inference(forward_demodulation,[],[f385,f122])).
% 0.22/0.56  fof(f385,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5)) | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5))),
% 0.22/0.56    inference(subsumption_resolution,[],[f384,f267])).
% 0.22/0.56  fof(f384,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5)) | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f379,f40])).
% 0.22/0.56  fof(f379,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK5)) | g1_orders_2(u1_struct_0(sK5),u1_orders_2(sK5)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK5)) | ~l1_orders_2(sK5) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f378,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK10(X0,X1,X2),sK11(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f378,plain,(
% 0.22/0.56    ( ! [X0] : (r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f377,f267])).
% 0.22/0.56  fof(f377,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~l1_orders_2(X0) | sP0(sK5,sK6,sK4)) )),
% 0.22/0.56    inference(resolution,[],[f376,f130])).
% 0.22/0.56  fof(f376,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f375,f267])).
% 0.22/0.56  fof(f375,plain,(
% 0.22/0.56    ( ! [X0] : (r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~l1_orders_2(X0) | sP0(sK5,sK6,sK4)) )),
% 0.22/0.56    inference(resolution,[],[f374,f129])).
% 0.22/0.56  fof(f374,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f373,f78])).
% 0.22/0.56  fof(f373,plain,(
% 0.22/0.56    ( ! [X0] : (r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f371,f38])).
% 0.22/0.56  fof(f371,plain,(
% 0.22/0.56    ( ! [X0] : (r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~l1_orders_2(X0) | ~l1_orders_2(sK3)) )),
% 0.22/0.56    inference(resolution,[],[f370,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X4,X0,X5,X1] : (~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X5) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r1_orders_2(X0,X2,X3) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X1)) | ~l1_orders_2(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_orders_2(X0,X2,X3) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_yellow_6)).
% 0.22/0.56  fof(f370,plain,(
% 0.22/0.56    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f369,f267])).
% 0.22/0.56  fof(f369,plain,(
% 0.22/0.56    r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f368,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ( ! [X6,X7] : (m1_subset_1(sK8(X6,X7,sK4),u1_struct_0(sK2)) | sP0(X6,X7,sK4)) )),
% 0.22/0.56    inference(superposition,[],[f58,f97])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f368,plain,(
% 0.22/0.56    ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f367,f267])).
% 0.22/0.56  fof(f367,plain,(
% 0.22/0.56    ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f366,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X4,X5] : (m1_subset_1(sK9(X4,X5,sK4),u1_struct_0(sK2)) | sP0(X4,X5,sK4)) )),
% 0.22/0.56    inference(superposition,[],[f59,f97])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f366,plain,(
% 0.22/0.56    ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f365,f267])).
% 0.22/0.56  fof(f365,plain,(
% 0.22/0.56    ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f364,f130])).
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f363,f267])).
% 0.22/0.56  fof(f363,plain,(
% 0.22/0.56    ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4)) | sP0(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f362,f129])).
% 0.22/0.56  fof(f362,plain,(
% 0.22/0.56    ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f361,f37])).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~l1_orders_2(sK2) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(subsumption_resolution,[],[f360,f77])).
% 0.22/0.56  fof(f360,plain,(
% 0.22/0.56    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) != k7_lattice3(k7_lattice3(sK2)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(sK3)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(sK2)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(sK2)) | ~l1_orders_2(sK2) | r1_orders_2(sK3,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))),
% 0.22/0.56    inference(resolution,[],[f357,f240])).
% 0.22/0.56  fof(f240,plain,(
% 0.22/0.56    sP0(sK3,sK6,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f239,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    v5_orders_3(sK6,sK2,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f27])).
% 0.22/0.56  fof(f239,plain,(
% 0.22/0.56    ~v5_orders_3(sK6,sK2,sK3) | sP0(sK3,sK6,sK2)),
% 0.22/0.56    inference(resolution,[],[f233,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v5_orders_3(X1,X0,X2) | sP0(X2,X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f233,plain,(
% 0.22/0.56    sP1(sK2,sK6,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f232,f43])).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    sP1(sK2,sK6,sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f229,f38])).
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    sP1(sK2,sK6,sK3) | ~l1_orders_2(sK3) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.22/0.56    inference(resolution,[],[f221,f42])).
% 0.22/0.56  fof(f221,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(X0)) | sP1(sK2,sK6,X0) | ~l1_orders_2(X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))) )),
% 0.22/0.56    inference(resolution,[],[f182,f37])).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~sP0(X0,sK6,X1) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(sK2)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X0,sK10(sK5,sK6,sK4),sK11(sK5,sK6,sK4))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f356,f268])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    k1_funct_1(sK6,sK9(sK5,sK6,sK4)) = sK11(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f267,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK9(X0,X1,X2)) = sK11(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f356,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != k7_lattice3(k7_lattice3(sK2)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f355,f77])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f354,f97])).
% 0.22/0.56  fof(f354,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK2)) | ~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f353,f163])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    u1_orders_2(sK2) = u1_orders_2(sK4)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f159])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    k7_lattice3(k7_lattice3(sK2)) != k7_lattice3(k7_lattice3(sK2)) | u1_orders_2(sK2) = u1_orders_2(sK4)),
% 0.22/0.56    inference(superposition,[],[f152,f77])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    ( ! [X0,X1] : (g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK2)) | u1_orders_2(sK4) = X1) )),
% 0.22/0.56    inference(superposition,[],[f117,f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    k7_lattice3(k7_lattice3(sK2)) = g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK4))),
% 0.22/0.56    inference(backward_demodulation,[],[f81,f97])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ( ! [X4,X3] : (g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK4)) != g1_orders_2(X3,X4) | u1_orders_2(sK4) = X4) )),
% 0.22/0.56    inference(resolution,[],[f68,f109])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f39])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) | ~l1_orders_2(sK4)),
% 0.22/0.56    inference(superposition,[],[f53,f97])).
% 0.22/0.56  fof(f353,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK11(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f352,f268])).
% 0.22/0.56  fof(f352,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f351,f267])).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | sP0(sK5,sK6,sK4) | ~m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f348,f39])).
% 0.22/0.56  fof(f348,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(sK10(sK5,sK6,sK4),u1_struct_0(X0)) | ~m1_subset_1(sK9(sK5,sK6,sK4),u1_struct_0(X1)) | ~m1_subset_1(sK8(sK5,sK6,sK4),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~l1_orders_2(sK4) | sP0(sK5,sK6,sK4) | ~m1_subset_1(k1_funct_1(sK6,sK9(sK5,sK6,sK4)),u1_struct_0(X0)) | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) | r1_orders_2(X0,sK10(sK5,sK6,sK4),k1_funct_1(sK6,sK9(sK5,sK6,sK4))) | ~sP0(X0,sK6,X1)) )),
% 0.22/0.56    inference(superposition,[],[f291,f269])).
% 0.22/0.56  fof(f269,plain,(
% 0.22/0.56    k1_funct_1(sK6,sK8(sK5,sK6,sK4)) = sK10(sK5,sK6,sK4)),
% 0.22/0.56    inference(resolution,[],[f267,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,sK8(X0,X1,X2)) = sK10(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    ( ! [X6,X10,X8,X7,X5,X9] : (~m1_subset_1(k1_funct_1(X9,sK8(X7,X8,X6)),u1_struct_0(X10)) | ~m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5)) | ~m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5)) | ~l1_orders_2(X5) | ~l1_orders_2(X6) | sP0(X7,X8,X6) | ~m1_subset_1(k1_funct_1(X9,sK9(X7,X8,X6)),u1_struct_0(X10)) | g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) | r1_orders_2(X10,k1_funct_1(X9,sK8(X7,X8,X6)),k1_funct_1(X9,sK9(X7,X8,X6))) | ~sP0(X10,X9,X5)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f290])).
% 0.22/0.56  fof(f290,plain,(
% 0.22/0.56    ( ! [X6,X10,X8,X7,X5,X9] : (g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6)) | ~m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5)) | ~m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5)) | ~l1_orders_2(X5) | ~l1_orders_2(X6) | sP0(X7,X8,X6) | ~m1_subset_1(k1_funct_1(X9,sK9(X7,X8,X6)),u1_struct_0(X10)) | ~m1_subset_1(k1_funct_1(X9,sK8(X7,X8,X6)),u1_struct_0(X10)) | r1_orders_2(X10,k1_funct_1(X9,sK8(X7,X8,X6)),k1_funct_1(X9,sK9(X7,X8,X6))) | ~m1_subset_1(sK9(X7,X8,X6),u1_struct_0(X5)) | ~m1_subset_1(sK8(X7,X8,X6),u1_struct_0(X5)) | ~sP0(X10,X9,X5)) )),
% 0.22/0.56    inference(resolution,[],[f280,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X2,X0,X8,X7,X1] : (~r1_orders_2(X2,X7,X8) | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(k1_funct_1(X1,X7),u1_struct_0(X0)) | r1_orders_2(X0,k1_funct_1(X1,X7),k1_funct_1(X1,X8)) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X8,X7,X1,X9] : (r1_orders_2(X0,X9,k1_funct_1(X1,X8)) | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(k1_funct_1(X1,X8),u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(equality_resolution,[],[f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X2,X0,X10,X8,X7,X1,X9] : (r1_orders_2(X0,X9,X10) | k1_funct_1(X1,X8) != X10 | k1_funct_1(X1,X7) != X9 | ~m1_subset_1(X10,u1_struct_0(X0)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_orders_2(X2,X7,X8) | ~m1_subset_1(X8,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f280,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) | ~m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0)) | ~m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~l1_orders_2(X3) | sP0(X1,X2,X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f279,f58])).
% 0.22/0.56  fof(f279,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) | ~m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0)) | ~m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0)) | ~m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X3)) | ~l1_orders_2(X0) | ~l1_orders_2(X3) | sP0(X1,X2,X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f278,f59])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK8(X1,X2,X3),sK9(X1,X2,X3)) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) | ~m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X0)) | ~m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X0)) | ~m1_subset_1(sK9(X1,X2,X3),u1_struct_0(X3)) | ~m1_subset_1(sK8(X1,X2,X3),u1_struct_0(X3)) | ~l1_orders_2(X0) | ~l1_orders_2(X3) | sP0(X1,X2,X3)) )),
% 0.22/0.56    inference(resolution,[],[f70,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_orders_2(X2,sK8(X0,X1,X2),sK9(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (7277)------------------------------
% 0.22/0.56  % (7277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7277)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (7277)Memory used [KB]: 6652
% 0.22/0.56  % (7277)Time elapsed: 0.115 s
% 0.22/0.56  % (7277)------------------------------
% 0.22/0.56  % (7277)------------------------------
% 1.53/0.56  % (7273)Success in time 0.193 s
%------------------------------------------------------------------------------
