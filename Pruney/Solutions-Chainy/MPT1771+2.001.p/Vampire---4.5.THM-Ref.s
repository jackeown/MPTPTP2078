%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:47 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  314 (8836 expanded)
%              Number of leaves         :   26 (4862 expanded)
%              Depth                    :   33
%              Number of atoms          : 1917 (155411 expanded)
%              Number of equality atoms :  116 (11704 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2643,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f744,f746,f748,f1504,f1640,f1901,f2136,f2642])).

fof(f2642,plain,
    ( ~ spl7_4
    | ~ spl7_26 ),
    inference(avatar_contradiction_clause,[],[f2641])).

fof(f2641,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f2640,f91])).

fof(f91,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(superposition,[],[f68,f66])).

fof(f66,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f47,f46,f45,f44,f43,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f68,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f48])).

fof(f2640,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(superposition,[],[f755,f2360])).

fof(f2360,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f2359,f1503])).

fof(f1503,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1501,plain,
    ( spl7_26
  <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f2359,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) ),
    inference(forward_demodulation,[],[f2358,f1626])).

fof(f1626,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) ),
    inference(superposition,[],[f470,f557])).

fof(f557,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f556,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f556,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f555,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f555,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f554,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f554,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f403,f94])).

fof(f94,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f403,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f402,f358])).

fof(f358,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f357,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f357,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f356,f54])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f356,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f355,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f355,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f354,f60])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f354,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f353,f61])).

fof(f61,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f353,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f138,f62])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f138,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f137,f50])).

fof(f137,plain,(
    ! [X2,X3] :
      ( k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f51])).

fof(f136,plain,(
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
    inference(subsumption_resolution,[],[f131,f52])).

fof(f131,plain,(
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
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f402,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f401,f53])).

fof(f401,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f400,f54])).

fof(f400,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f399,f55])).

fof(f399,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f398,f60])).

fof(f398,plain,(
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
    inference(subsumption_resolution,[],[f397,f61])).

fof(f397,plain,(
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
    inference(resolution,[],[f160,f62])).

fof(f160,plain,(
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
    inference(subsumption_resolution,[],[f157,f109])).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK0,X1)
      | m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f157,plain,(
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
    inference(resolution,[],[f72,f59])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f470,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) ),
    inference(subsumption_resolution,[],[f469,f53])).

fof(f469,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f468,f54])).

fof(f468,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f467,f55])).

fof(f467,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f466,f243])).

fof(f243,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f242,f50])).

fof(f242,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f51])).

fof(f241,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f240,f52])).

fof(f240,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f94])).

fof(f232,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f59])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,(
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
    inference(subsumption_resolution,[],[f125,f60])).

fof(f125,plain,(
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
    inference(subsumption_resolution,[],[f124,f61])).

fof(f124,plain,(
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
    inference(resolution,[],[f84,f62])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f466,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f455,f284])).

fof(f284,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f283,f50])).

fof(f283,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f282,f51])).

fof(f282,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f281,f52])).

fof(f281,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f273,f94])).

fof(f273,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f147,f59])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f146,f53])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,(
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
    inference(subsumption_resolution,[],[f143,f60])).

fof(f143,plain,(
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
    inference(subsumption_resolution,[],[f142,f61])).

fof(f142,plain,(
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
    inference(resolution,[],[f85,f62])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f455,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f301,f141])).

fof(f141,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f140,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f140,plain,(
    ! [X4,X5] :
      ( k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f139,f107])).

fof(f107,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f106,f51])).

fof(f106,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f102,f52])).

fof(f102,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f139,plain,(
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
    inference(subsumption_resolution,[],[f132,f100])).

fof(f100,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f97,f52])).

fof(f97,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f132,plain,(
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
    inference(resolution,[],[f74,f63])).

fof(f63,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f301,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f300,f50])).

fof(f300,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f299,f51])).

fof(f299,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f298,f52])).

fof(f298,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f290,f94])).

fof(f290,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f153,f59])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f152,f53])).

fof(f152,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f151,f54])).

fof(f151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f150,f55])).

fof(f150,plain,(
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
    inference(subsumption_resolution,[],[f149,f60])).

fof(f149,plain,(
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
    inference(subsumption_resolution,[],[f148,f61])).

fof(f148,plain,(
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
    inference(resolution,[],[f86,f62])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f2358,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f2357,f557])).

fof(f2357,plain,(
    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f2356,f50])).

fof(f2356,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2355,f51])).

fof(f2355,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2353,f52])).

fof(f2353,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f465,f59])).

fof(f465,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f464,f53])).

fof(f464,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f463,f54])).

fof(f463,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f462,f55])).

fof(f462,plain,(
    ! [X0] :
      ( k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f461,f243])).

fof(f461,plain,(
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
    inference(subsumption_resolution,[],[f454,f284])).

fof(f454,plain,(
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
    inference(resolution,[],[f301,f161])).

fof(f161,plain,(
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
    inference(subsumption_resolution,[],[f158,f110])).

fof(f110,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK3,X2)
      | m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f78,f63])).

fof(f158,plain,(
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
    inference(resolution,[],[f72,f63])).

fof(f755,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f754,f63])).

fof(f754,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f750,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f750,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5)
    | ~ spl7_4 ),
    inference(resolution,[],[f184,f90])).

fof(f90,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f65,f66])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl7_4
  <=> ! [X0] :
        ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f2136,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f2135])).

fof(f2135,plain,
    ( $false
    | spl7_25 ),
    inference(subsumption_resolution,[],[f2134,f1499])).

fof(f1499,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1497,plain,
    ( spl7_25
  <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f2134,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f2133,f557])).

fof(f2133,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f2132,f50])).

fof(f2132,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2131,f51])).

fof(f2131,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2130,f52])).

fof(f2130,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2123,f59])).

fof(f2123,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f483,f57])).

fof(f57,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f483,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,X4)
      | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f482,f53])).

fof(f482,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f481,f54])).

fof(f481,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f480,f55])).

fof(f480,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f479,f243])).

fof(f479,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f457,f284])).

fof(f457,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f301,f86])).

fof(f1901,plain,(
    spl7_24 ),
    inference(avatar_contradiction_clause,[],[f1900])).

fof(f1900,plain,
    ( $false
    | spl7_24 ),
    inference(subsumption_resolution,[],[f1899,f1495])).

fof(f1495,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f1493])).

fof(f1493,plain,
    ( spl7_24
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1899,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1898,f557])).

fof(f1898,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1897,f50])).

fof(f1897,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1896,f51])).

fof(f1896,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1895,f52])).

fof(f1895,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1888,f59])).

fof(f1888,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f488,f57])).

fof(f488,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,X6)
      | v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f487,f53])).

fof(f487,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f486,f54])).

fof(f486,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f485,f55])).

fof(f485,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f484,f243])).

fof(f484,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f458,f284])).

fof(f458,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f301,f85])).

fof(f1640,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f1639])).

fof(f1639,plain,
    ( $false
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1638,f1491])).

fof(f1491,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f1489])).

fof(f1489,plain,
    ( spl7_23
  <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1638,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(forward_demodulation,[],[f1637,f557])).

fof(f1637,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) ),
    inference(subsumption_resolution,[],[f1636,f50])).

fof(f1636,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1635,f51])).

fof(f1635,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1634,f52])).

fof(f1634,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1627,f59])).

fof(f1627,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f493,f57])).

fof(f493,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X9,X8)
      | v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(sK3,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f492,f53])).

fof(f492,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f491,f54])).

fof(f491,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f490,f55])).

fof(f490,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f489,f243])).

fof(f489,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f459,f284])).

fof(f459,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(resolution,[],[f301,f84])).

fof(f1504,plain,
    ( ~ spl7_23
    | ~ spl7_24
    | ~ spl7_25
    | spl7_26 ),
    inference(avatar_split_clause,[],[f1487,f1501,f1497,f1493,f1489])).

fof(f1487,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f1486,f739])).

fof(f739,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(superposition,[],[f239,f553])).

fof(f553,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f552,f50])).

fof(f552,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f551,f51])).

fof(f551,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f550,f52])).

fof(f550,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f396,f94])).

fof(f396,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f395,f311])).

fof(f311,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f310,f53])).

fof(f310,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f309,f54])).

fof(f309,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f308,f55])).

fof(f308,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f307,f60])).

fof(f307,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f306,f61])).

fof(f306,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f135,f62])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f134,f50])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,(
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
    inference(subsumption_resolution,[],[f130,f52])).

fof(f130,plain,(
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
    inference(resolution,[],[f74,f57])).

fof(f395,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f394,f53])).

fof(f394,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f393,f54])).

fof(f393,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f392,f55])).

fof(f392,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f391,f60])).

fof(f391,plain,(
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
    inference(subsumption_resolution,[],[f390,f61])).

fof(f390,plain,(
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
    inference(resolution,[],[f159,f62])).

fof(f159,plain,(
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
    inference(subsumption_resolution,[],[f156,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f78,f57])).

fof(f156,plain,(
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
    inference(resolution,[],[f72,f57])).

fof(f239,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f238,f50])).

fof(f238,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f237,f51])).

fof(f237,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f236,f52])).

fof(f236,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f231,f94])).

fof(f231,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f57])).

fof(f1486,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f1485,f738])).

fof(f738,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f280,f553])).

fof(f280,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f279,f50])).

fof(f279,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f278,f51])).

fof(f278,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f52])).

fof(f277,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f272,f94])).

fof(f272,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f147,f57])).

fof(f1485,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f1484,f737])).

fof(f737,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f297,f553])).

fof(f297,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f296,f50])).

fof(f296,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f295,f51])).

fof(f295,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f294,f52])).

fof(f294,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f289,f94])).

fof(f289,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f153,f57])).

fof(f1484,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(resolution,[],[f666,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f666,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f665,f557])).

fof(f665,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f664,f553])).

fof(f664,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f663,f50])).

fof(f663,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f662,f51])).

fof(f662,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f661,f52])).

fof(f661,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f389,f94])).

fof(f389,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(sK0,X5)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f388,f58])).

fof(f388,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f387,f56])).

fof(f387,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4))
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f364,f59])).

fof(f364,plain,(
    ! [X5] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(resolution,[],[f194,f63])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X2)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f193,f78])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f192,f78])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f191,f53])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f190,f54])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f189,f55])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f188,f50])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f187,f60])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f186,f61])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(sK0,X1)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f73,f62])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_pre_topc(X4,X3)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_pre_topc(X4,X3)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f748,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f742,f173])).

fof(f173,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_1
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f742,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(superposition,[],[f243,f557])).

fof(f746,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f741,f177])).

fof(f177,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_2
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f741,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(superposition,[],[f284,f557])).

fof(f744,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f740,f181])).

fof(f181,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl7_3
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f740,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f301,f557])).

fof(f185,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f169,f183,f179,f175,f171])).

fof(f169,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ) ),
    inference(subsumption_resolution,[],[f168,f53])).

fof(f168,plain,(
    ! [X0] :
      ( r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f167,f54])).

fof(f167,plain,(
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
    inference(subsumption_resolution,[],[f166,f55])).

fof(f166,plain,(
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
    inference(subsumption_resolution,[],[f165,f58])).

fof(f165,plain,(
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
    inference(subsumption_resolution,[],[f164,f107])).

fof(f164,plain,(
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
    inference(subsumption_resolution,[],[f163,f100])).

fof(f163,plain,(
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
    inference(subsumption_resolution,[],[f162,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f162,plain,(
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
    inference(resolution,[],[f87,f67])).

fof(f67,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
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
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:12:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.53  % (23755)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (23770)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (23760)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.56  % (23756)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.57  % (23751)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.57  % (23764)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (23771)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.57  % (23761)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  % (23752)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (23751)Refutation not found, incomplete strategy% (23751)------------------------------
% 0.22/0.57  % (23751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (23751)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (23751)Memory used [KB]: 10618
% 0.22/0.57  % (23751)Time elapsed: 0.138 s
% 0.22/0.57  % (23751)------------------------------
% 0.22/0.57  % (23751)------------------------------
% 0.22/0.58  % (23754)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.59  % (23753)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.59  % (23767)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.59  % (23768)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.58/0.59  % (23759)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.58/0.59  % (23757)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.58/0.60  % (23766)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.58/0.60  % (23774)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.58/0.60  % (23769)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.58/0.60  % (23772)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.89/0.61  % (23758)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.89/0.62  % (23765)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.89/0.62  % (23762)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.89/0.63  % (23773)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.89/0.64  % (23776)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.89/0.64  % (23775)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.89/0.65  % (23763)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 2.29/0.74  % (23761)Refutation found. Thanks to Tanya!
% 2.29/0.74  % SZS status Theorem for theBenchmark
% 2.29/0.74  % SZS output start Proof for theBenchmark
% 2.29/0.74  fof(f2643,plain,(
% 2.29/0.74    $false),
% 2.29/0.74    inference(avatar_sat_refutation,[],[f185,f744,f746,f748,f1504,f1640,f1901,f2136,f2642])).
% 2.29/0.74  fof(f2642,plain,(
% 2.29/0.74    ~spl7_4 | ~spl7_26),
% 2.29/0.74    inference(avatar_contradiction_clause,[],[f2641])).
% 2.29/0.74  fof(f2641,plain,(
% 2.29/0.74    $false | (~spl7_4 | ~spl7_26)),
% 2.29/0.74    inference(subsumption_resolution,[],[f2640,f91])).
% 2.29/0.74  fof(f91,plain,(
% 2.29/0.74    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 2.29/0.74    inference(superposition,[],[f68,f66])).
% 2.29/0.74  fof(f66,plain,(
% 2.29/0.74    sK5 = sK6),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f48,plain,(
% 2.29/0.74    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.29/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f47,f46,f45,f44,f43,f42,f41])).
% 2.29/0.74  fof(f41,plain,(
% 2.29/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f42,plain,(
% 2.29/0.74    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f43,plain,(
% 2.29/0.74    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f44,plain,(
% 2.29/0.74    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f45,plain,(
% 2.29/0.74    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f46,plain,(
% 2.29/0.74    ? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f47,plain,(
% 2.29/0.74    ? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 2.29/0.74    introduced(choice_axiom,[])).
% 2.29/0.74  fof(f17,plain,(
% 2.29/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.29/0.74    inference(flattening,[],[f16])).
% 2.29/0.74  fof(f16,plain,(
% 2.29/0.74    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.29/0.74    inference(ennf_transformation,[],[f15])).
% 2.29/0.74  fof(f15,negated_conjecture,(
% 2.29/0.74    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 2.29/0.74    inference(negated_conjecture,[],[f14])).
% 2.29/0.74  fof(f14,conjecture,(
% 2.29/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 2.29/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).
% 2.29/0.74  fof(f68,plain,(
% 2.29/0.74    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f2640,plain,(
% 2.29/0.74    r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | (~spl7_4 | ~spl7_26)),
% 2.29/0.74    inference(superposition,[],[f755,f2360])).
% 2.29/0.74  fof(f2360,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) | ~spl7_26),
% 2.29/0.74    inference(forward_demodulation,[],[f2359,f1503])).
% 2.29/0.74  fof(f1503,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~spl7_26),
% 2.29/0.74    inference(avatar_component_clause,[],[f1501])).
% 2.29/0.74  fof(f1501,plain,(
% 2.29/0.74    spl7_26 <=> k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))),
% 2.29/0.74    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.29/0.74  fof(f2359,plain,(
% 2.29/0.74    k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2)),
% 2.29/0.74    inference(forward_demodulation,[],[f2358,f1626])).
% 2.29/0.74  fof(f1626,plain,(
% 2.29/0.74    k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2))),
% 2.29/0.74    inference(superposition,[],[f470,f557])).
% 2.29/0.74  fof(f557,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),
% 2.29/0.74    inference(subsumption_resolution,[],[f556,f50])).
% 2.29/0.74  fof(f50,plain,(
% 2.29/0.74    ~v2_struct_0(sK0)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f556,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | v2_struct_0(sK0)),
% 2.29/0.74    inference(subsumption_resolution,[],[f555,f51])).
% 2.29/0.74  fof(f51,plain,(
% 2.29/0.74    v2_pre_topc(sK0)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f555,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.29/0.74    inference(subsumption_resolution,[],[f554,f52])).
% 2.29/0.74  fof(f52,plain,(
% 2.29/0.74    l1_pre_topc(sK0)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f554,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.29/0.74    inference(resolution,[],[f403,f94])).
% 2.29/0.74  fof(f94,plain,(
% 2.29/0.74    m1_pre_topc(sK0,sK0)),
% 2.29/0.74    inference(resolution,[],[f70,f52])).
% 2.29/0.74  fof(f70,plain,(
% 2.29/0.74    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 2.29/0.74    inference(cnf_transformation,[],[f19])).
% 2.29/0.74  fof(f19,plain,(
% 2.29/0.74    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.29/0.74    inference(ennf_transformation,[],[f10])).
% 2.29/0.74  fof(f10,axiom,(
% 2.29/0.74    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.29/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.29/0.74  fof(f403,plain,(
% 2.29/0.74    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.74    inference(forward_demodulation,[],[f402,f358])).
% 2.29/0.74  fof(f358,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 2.29/0.74    inference(subsumption_resolution,[],[f357,f53])).
% 2.29/0.74  fof(f53,plain,(
% 2.29/0.74    ~v2_struct_0(sK1)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f357,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 2.29/0.74    inference(subsumption_resolution,[],[f356,f54])).
% 2.29/0.74  fof(f54,plain,(
% 2.29/0.74    v2_pre_topc(sK1)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f356,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.29/0.74    inference(subsumption_resolution,[],[f355,f55])).
% 2.29/0.74  fof(f55,plain,(
% 2.29/0.74    l1_pre_topc(sK1)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f355,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.29/0.74    inference(subsumption_resolution,[],[f354,f60])).
% 2.29/0.74  fof(f60,plain,(
% 2.29/0.74    v1_funct_1(sK4)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f354,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.29/0.74    inference(subsumption_resolution,[],[f353,f61])).
% 2.29/0.74  fof(f61,plain,(
% 2.29/0.74    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f353,plain,(
% 2.29/0.74    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.29/0.74    inference(resolution,[],[f138,f62])).
% 2.29/0.74  fof(f62,plain,(
% 2.29/0.74    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f138,plain,(
% 2.29/0.74    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 2.29/0.74    inference(subsumption_resolution,[],[f137,f50])).
% 2.29/0.74  fof(f137,plain,(
% 2.29/0.74    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 2.29/0.74    inference(subsumption_resolution,[],[f136,f51])).
% 2.29/0.74  fof(f136,plain,(
% 2.29/0.74    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.29/0.74    inference(subsumption_resolution,[],[f131,f52])).
% 2.29/0.74  fof(f131,plain,(
% 2.29/0.74    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.29/0.74    inference(resolution,[],[f74,f59])).
% 2.29/0.74  fof(f59,plain,(
% 2.29/0.74    m1_pre_topc(sK3,sK0)),
% 2.29/0.74    inference(cnf_transformation,[],[f48])).
% 2.29/0.74  fof(f74,plain,(
% 2.29/0.74    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.74    inference(cnf_transformation,[],[f26])).
% 2.29/0.74  fof(f26,plain,(
% 2.29/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.29/0.74    inference(flattening,[],[f25])).
% 2.29/0.74  fof(f25,plain,(
% 2.29/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.29/0.74    inference(ennf_transformation,[],[f6])).
% 2.29/0.75  fof(f6,axiom,(
% 2.29/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.29/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.29/0.75  fof(f402,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(subsumption_resolution,[],[f401,f53])).
% 2.29/0.75  fof(f401,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(subsumption_resolution,[],[f400,f54])).
% 2.29/0.75  fof(f400,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(subsumption_resolution,[],[f399,f55])).
% 2.29/0.75  fof(f399,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(subsumption_resolution,[],[f398,f60])).
% 2.29/0.75  fof(f398,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(subsumption_resolution,[],[f397,f61])).
% 2.29/0.75  fof(f397,plain,(
% 2.29/0.75    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.29/0.75    inference(resolution,[],[f160,f62])).
% 2.94/0.75  fof(f160,plain,(
% 2.94/0.75    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f157,f109])).
% 2.94/0.75  fof(f109,plain,(
% 2.94/0.75    ( ! [X1] : (~m1_pre_topc(sK0,X1) | m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 2.94/0.75    inference(resolution,[],[f78,f59])).
% 2.94/0.75  fof(f78,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f34])).
% 2.94/0.75  fof(f34,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.94/0.75    inference(flattening,[],[f33])).
% 2.94/0.75  fof(f33,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.94/0.75    inference(ennf_transformation,[],[f13])).
% 2.94/0.75  fof(f13,axiom,(
% 2.94/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.94/0.75  fof(f157,plain,(
% 2.94/0.75    ( ! [X4,X5,X3] : (k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 2.94/0.75    inference(resolution,[],[f72,f59])).
% 2.94/0.75  fof(f72,plain,(
% 2.94/0.75    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f22])).
% 2.94/0.75  fof(f22,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/0.75    inference(flattening,[],[f21])).
% 2.94/0.75  fof(f21,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/0.75    inference(ennf_transformation,[],[f7])).
% 2.94/0.75  fof(f7,axiom,(
% 2.94/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.94/0.75  fof(f470,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2)),
% 2.94/0.75    inference(subsumption_resolution,[],[f469,f53])).
% 2.94/0.75  fof(f469,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | v2_struct_0(sK1)),
% 2.94/0.75    inference(subsumption_resolution,[],[f468,f54])).
% 2.94/0.75  fof(f468,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.75    inference(subsumption_resolution,[],[f467,f55])).
% 2.94/0.75  fof(f467,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.75    inference(subsumption_resolution,[],[f466,f243])).
% 2.94/0.75  fof(f243,plain,(
% 2.94/0.75    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 2.94/0.75    inference(subsumption_resolution,[],[f242,f50])).
% 2.94/0.75  fof(f242,plain,(
% 2.94/0.75    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f241,f51])).
% 2.94/0.75  fof(f241,plain,(
% 2.94/0.75    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f240,f52])).
% 2.94/0.75  fof(f240,plain,(
% 2.94/0.75    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f232,f94])).
% 2.94/0.75  fof(f232,plain,(
% 2.94/0.75    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(resolution,[],[f129,f59])).
% 2.94/0.75  fof(f129,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f128,f53])).
% 2.94/0.75  fof(f128,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f127,f54])).
% 2.94/0.75  fof(f127,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f126,f55])).
% 2.94/0.75  fof(f126,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f125,f60])).
% 2.94/0.75  fof(f125,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f124,f61])).
% 2.94/0.75  fof(f124,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(resolution,[],[f84,f62])).
% 2.94/0.75  fof(f84,plain,(
% 2.94/0.75    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f40])).
% 2.94/0.75  fof(f40,plain,(
% 2.94/0.75    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/0.75    inference(flattening,[],[f39])).
% 2.94/0.75  fof(f39,plain,(
% 2.94/0.75    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/0.75    inference(ennf_transformation,[],[f9])).
% 2.94/0.75  fof(f9,axiom,(
% 2.94/0.75    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 2.94/0.75  fof(f466,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.75    inference(subsumption_resolution,[],[f455,f284])).
% 2.94/0.75  fof(f284,plain,(
% 2.94/0.75    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.94/0.75    inference(subsumption_resolution,[],[f283,f50])).
% 2.94/0.75  fof(f283,plain,(
% 2.94/0.75    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f282,f51])).
% 2.94/0.75  fof(f282,plain,(
% 2.94/0.75    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f281,f52])).
% 2.94/0.75  fof(f281,plain,(
% 2.94/0.75    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f273,f94])).
% 2.94/0.75  fof(f273,plain,(
% 2.94/0.75    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(resolution,[],[f147,f59])).
% 2.94/0.75  fof(f147,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f146,f53])).
% 2.94/0.75  fof(f146,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f145,f54])).
% 2.94/0.75  fof(f145,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f144,f55])).
% 2.94/0.75  fof(f144,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f143,f60])).
% 2.94/0.75  fof(f143,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f142,f61])).
% 2.94/0.75  fof(f142,plain,(
% 2.94/0.75    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(resolution,[],[f85,f62])).
% 2.94/0.75  fof(f85,plain,(
% 2.94/0.75    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f40])).
% 2.94/0.75  fof(f455,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK0,sK3,sK4),sK2) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.75    inference(resolution,[],[f301,f141])).
% 2.94/0.75  fof(f141,plain,(
% 2.94/0.75    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f140,f58])).
% 2.94/0.75  fof(f58,plain,(
% 2.94/0.75    ~v2_struct_0(sK3)),
% 2.94/0.75    inference(cnf_transformation,[],[f48])).
% 2.94/0.75  fof(f140,plain,(
% 2.94/0.75    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | v2_struct_0(sK3)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f139,f107])).
% 2.94/0.75  fof(f107,plain,(
% 2.94/0.75    v2_pre_topc(sK3)),
% 2.94/0.75    inference(subsumption_resolution,[],[f106,f51])).
% 2.94/0.75  fof(f106,plain,(
% 2.94/0.75    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f102,f52])).
% 2.94/0.75  fof(f102,plain,(
% 2.94/0.75    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.94/0.75    inference(resolution,[],[f77,f59])).
% 2.94/0.75  fof(f77,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f32])).
% 2.94/0.75  fof(f32,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.94/0.75    inference(flattening,[],[f31])).
% 2.94/0.75  fof(f31,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.94/0.75    inference(ennf_transformation,[],[f2])).
% 2.94/0.75  fof(f2,axiom,(
% 2.94/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.94/0.75  fof(f139,plain,(
% 2.94/0.75    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f132,f100])).
% 2.94/0.75  fof(f100,plain,(
% 2.94/0.75    l1_pre_topc(sK3)),
% 2.94/0.75    inference(subsumption_resolution,[],[f97,f52])).
% 2.94/0.75  fof(f97,plain,(
% 2.94/0.75    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 2.94/0.75    inference(resolution,[],[f71,f59])).
% 2.94/0.75  fof(f71,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f20])).
% 2.94/0.75  fof(f20,plain,(
% 2.94/0.75    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.94/0.75    inference(ennf_transformation,[],[f4])).
% 2.94/0.75  fof(f4,axiom,(
% 2.94/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.94/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.94/0.75  fof(f132,plain,(
% 2.94/0.75    ( ! [X4,X5] : (k2_tmap_1(sK3,X4,X5,sK2) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X4),X5,u1_struct_0(sK2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.94/0.75    inference(resolution,[],[f74,f63])).
% 2.94/0.75  fof(f63,plain,(
% 2.94/0.75    m1_pre_topc(sK2,sK3)),
% 2.94/0.75    inference(cnf_transformation,[],[f48])).
% 2.94/0.75  fof(f301,plain,(
% 2.94/0.75    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.94/0.75    inference(subsumption_resolution,[],[f300,f50])).
% 2.94/0.75  fof(f300,plain,(
% 2.94/0.75    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f299,f51])).
% 2.94/0.75  fof(f299,plain,(
% 2.94/0.75    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f298,f52])).
% 2.94/0.75  fof(f298,plain,(
% 2.94/0.75    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f290,f94])).
% 2.94/0.75  fof(f290,plain,(
% 2.94/0.75    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(resolution,[],[f153,f59])).
% 2.94/0.75  fof(f153,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f152,f53])).
% 2.94/0.75  fof(f152,plain,(
% 2.94/0.75    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f151,f54])).
% 2.94/0.75  fof(f151,plain,(
% 2.94/0.75    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f150,f55])).
% 2.94/0.75  fof(f150,plain,(
% 2.94/0.75    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f149,f60])).
% 2.94/0.75  fof(f149,plain,(
% 2.94/0.75    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f148,f61])).
% 2.94/0.75  fof(f148,plain,(
% 2.94/0.75    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(resolution,[],[f86,f62])).
% 2.94/0.75  fof(f86,plain,(
% 2.94/0.75    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f40])).
% 2.94/0.75  fof(f2358,plain,(
% 2.94/0.75    k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK2))),
% 2.94/0.75    inference(forward_demodulation,[],[f2357,f557])).
% 2.94/0.75  fof(f2357,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 2.94/0.75    inference(subsumption_resolution,[],[f2356,f50])).
% 2.94/0.75  fof(f2356,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f2355,f51])).
% 2.94/0.75  fof(f2355,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(subsumption_resolution,[],[f2353,f52])).
% 2.94/0.75  fof(f2353,plain,(
% 2.94/0.75    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.75    inference(resolution,[],[f465,f59])).
% 2.94/0.75  fof(f465,plain,(
% 2.94/0.75    ( ! [X0] : (~m1_pre_topc(sK3,X0) | k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f464,f53])).
% 2.94/0.75  fof(f464,plain,(
% 2.94/0.75    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f463,f54])).
% 2.94/0.75  fof(f463,plain,(
% 2.94/0.75    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f462,f55])).
% 2.94/0.75  fof(f462,plain,(
% 2.94/0.75    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f461,f243])).
% 2.94/0.75  fof(f461,plain,(
% 2.94/0.75    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.75    inference(subsumption_resolution,[],[f454,f284])).
% 2.94/0.76  fof(f454,plain,(
% 2.94/0.76    ( ! [X0] : (k3_tmap_1(X0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(resolution,[],[f301,f161])).
% 2.94/0.76  fof(f161,plain,(
% 2.94/0.76    ( ! [X6,X8,X7] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7)))) | k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2)) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f158,f110])).
% 2.94/0.76  fof(f110,plain,(
% 2.94/0.76    ( ! [X2] : (~m1_pre_topc(sK3,X2) | m1_pre_topc(sK2,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) )),
% 2.94/0.76    inference(resolution,[],[f78,f63])).
% 2.94/0.76  fof(f158,plain,(
% 2.94/0.76    ( ! [X6,X8,X7] : (k3_tmap_1(X6,X7,sK3,sK2,X8) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(X7),X8,u1_struct_0(sK2)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X7)))) | ~v1_funct_2(X8,u1_struct_0(sK3),u1_struct_0(X7)) | ~v1_funct_1(X8) | ~m1_pre_topc(sK2,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(resolution,[],[f72,f63])).
% 2.94/0.76  fof(f755,plain,(
% 2.94/0.76    r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 2.94/0.76    inference(subsumption_resolution,[],[f754,f63])).
% 2.94/0.76  fof(f754,plain,(
% 2.94/0.76    ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 2.94/0.76    inference(subsumption_resolution,[],[f750,f56])).
% 2.94/0.76  fof(f56,plain,(
% 2.94/0.76    ~v2_struct_0(sK2)),
% 2.94/0.76    inference(cnf_transformation,[],[f48])).
% 2.94/0.76  fof(f750,plain,(
% 2.94/0.76    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | r1_tmap_1(sK2,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK2),sK5) | ~spl7_4),
% 2.94/0.76    inference(resolution,[],[f184,f90])).
% 2.94/0.76  fof(f90,plain,(
% 2.94/0.76    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.94/0.76    inference(forward_demodulation,[],[f65,f66])).
% 2.94/0.76  fof(f65,plain,(
% 2.94/0.76    m1_subset_1(sK6,u1_struct_0(sK2))),
% 2.94/0.76    inference(cnf_transformation,[],[f48])).
% 2.94/0.76  fof(f184,plain,(
% 2.94/0.76    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5)) ) | ~spl7_4),
% 2.94/0.76    inference(avatar_component_clause,[],[f183])).
% 2.94/0.76  fof(f183,plain,(
% 2.94/0.76    spl7_4 <=> ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.94/0.76  fof(f2136,plain,(
% 2.94/0.76    spl7_25),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f2135])).
% 2.94/0.76  fof(f2135,plain,(
% 2.94/0.76    $false | spl7_25),
% 2.94/0.76    inference(subsumption_resolution,[],[f2134,f1499])).
% 2.94/0.76  fof(f1499,plain,(
% 2.94/0.76    ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl7_25),
% 2.94/0.76    inference(avatar_component_clause,[],[f1497])).
% 2.94/0.76  fof(f1497,plain,(
% 2.94/0.76    spl7_25 <=> m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.94/0.76  fof(f2134,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.94/0.76    inference(forward_demodulation,[],[f2133,f557])).
% 2.94/0.76  fof(f2133,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.94/0.76    inference(subsumption_resolution,[],[f2132,f50])).
% 2.94/0.76  fof(f2132,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f2131,f51])).
% 2.94/0.76  fof(f2131,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f2130,f52])).
% 2.94/0.76  fof(f2130,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f2123,f59])).
% 2.94/0.76  fof(f2123,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f483,f57])).
% 2.94/0.76  fof(f57,plain,(
% 2.94/0.76    m1_pre_topc(sK2,sK0)),
% 2.94/0.76    inference(cnf_transformation,[],[f48])).
% 2.94/0.76  fof(f483,plain,(
% 2.94/0.76    ( ! [X4,X5] : (~m1_pre_topc(X5,X4) | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f482,f53])).
% 2.94/0.76  fof(f482,plain,(
% 2.94/0.76    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f481,f54])).
% 2.94/0.76  fof(f481,plain,(
% 2.94/0.76    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f480,f55])).
% 2.94/0.76  fof(f480,plain,(
% 2.94/0.76    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f479,f243])).
% 2.94/0.76  fof(f479,plain,(
% 2.94/0.76    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f457,f284])).
% 2.94/0.76  fof(f457,plain,(
% 2.94/0.76    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.94/0.76    inference(resolution,[],[f301,f86])).
% 2.94/0.76  fof(f1901,plain,(
% 2.94/0.76    spl7_24),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f1900])).
% 2.94/0.76  fof(f1900,plain,(
% 2.94/0.76    $false | spl7_24),
% 2.94/0.76    inference(subsumption_resolution,[],[f1899,f1495])).
% 2.94/0.76  fof(f1495,plain,(
% 2.94/0.76    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | spl7_24),
% 2.94/0.76    inference(avatar_component_clause,[],[f1493])).
% 2.94/0.76  fof(f1493,plain,(
% 2.94/0.76    spl7_24 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.94/0.76  fof(f1899,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.94/0.76    inference(forward_demodulation,[],[f1898,f557])).
% 2.94/0.76  fof(f1898,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.94/0.76    inference(subsumption_resolution,[],[f1897,f50])).
% 2.94/0.76  fof(f1897,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1896,f51])).
% 2.94/0.76  fof(f1896,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1895,f52])).
% 2.94/0.76  fof(f1895,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1888,f59])).
% 2.94/0.76  fof(f1888,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f488,f57])).
% 2.94/0.76  fof(f488,plain,(
% 2.94/0.76    ( ! [X6,X7] : (~m1_pre_topc(X7,X6) | v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f487,f53])).
% 2.94/0.76  fof(f487,plain,(
% 2.94/0.76    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f486,f54])).
% 2.94/0.76  fof(f486,plain,(
% 2.94/0.76    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f485,f55])).
% 2.94/0.76  fof(f485,plain,(
% 2.94/0.76    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f484,f243])).
% 2.94/0.76  fof(f484,plain,(
% 2.94/0.76    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f458,f284])).
% 2.94/0.76  fof(f458,plain,(
% 2.94/0.76    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 2.94/0.76    inference(resolution,[],[f301,f85])).
% 2.94/0.76  fof(f1640,plain,(
% 2.94/0.76    spl7_23),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f1639])).
% 2.94/0.76  fof(f1639,plain,(
% 2.94/0.76    $false | spl7_23),
% 2.94/0.76    inference(subsumption_resolution,[],[f1638,f1491])).
% 2.94/0.76  fof(f1491,plain,(
% 2.94/0.76    ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) | spl7_23),
% 2.94/0.76    inference(avatar_component_clause,[],[f1489])).
% 2.94/0.76  fof(f1489,plain,(
% 2.94/0.76    spl7_23 <=> v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.94/0.76  fof(f1638,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    inference(forward_demodulation,[],[f1637,f557])).
% 2.94/0.76  fof(f1637,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))),
% 2.94/0.76    inference(subsumption_resolution,[],[f1636,f50])).
% 2.94/0.76  fof(f1636,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1635,f51])).
% 2.94/0.76  fof(f1635,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1634,f52])).
% 2.94/0.76  fof(f1634,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f1627,f59])).
% 2.94/0.76  fof(f1627,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f493,f57])).
% 2.94/0.76  fof(f493,plain,(
% 2.94/0.76    ( ! [X8,X9] : (~m1_pre_topc(X9,X8) | v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f492,f53])).
% 2.94/0.76  fof(f492,plain,(
% 2.94/0.76    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f491,f54])).
% 2.94/0.76  fof(f491,plain,(
% 2.94/0.76    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f490,f55])).
% 2.94/0.76  fof(f490,plain,(
% 2.94/0.76    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f489,f243])).
% 2.94/0.76  fof(f489,plain,(
% 2.94/0.76    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f459,f284])).
% 2.94/0.76  fof(f459,plain,(
% 2.94/0.76    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 2.94/0.76    inference(resolution,[],[f301,f84])).
% 2.94/0.76  fof(f1504,plain,(
% 2.94/0.76    ~spl7_23 | ~spl7_24 | ~spl7_25 | spl7_26),
% 2.94/0.76    inference(avatar_split_clause,[],[f1487,f1501,f1497,f1493,f1489])).
% 2.94/0.76  fof(f1487,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    inference(subsumption_resolution,[],[f1486,f739])).
% 2.94/0.76  fof(f739,plain,(
% 2.94/0.76    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 2.94/0.76    inference(superposition,[],[f239,f553])).
% 2.94/0.76  fof(f553,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 2.94/0.76    inference(subsumption_resolution,[],[f552,f50])).
% 2.94/0.76  fof(f552,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f551,f51])).
% 2.94/0.76  fof(f551,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f550,f52])).
% 2.94/0.76  fof(f550,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f396,f94])).
% 2.94/0.76  fof(f396,plain,(
% 2.94/0.76    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(forward_demodulation,[],[f395,f311])).
% 2.94/0.76  fof(f311,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 2.94/0.76    inference(subsumption_resolution,[],[f310,f53])).
% 2.94/0.76  fof(f310,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 2.94/0.76    inference(subsumption_resolution,[],[f309,f54])).
% 2.94/0.76  fof(f309,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.76    inference(subsumption_resolution,[],[f308,f55])).
% 2.94/0.76  fof(f308,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.76    inference(subsumption_resolution,[],[f307,f60])).
% 2.94/0.76  fof(f307,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.76    inference(subsumption_resolution,[],[f306,f61])).
% 2.94/0.76  fof(f306,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 2.94/0.76    inference(resolution,[],[f135,f62])).
% 2.94/0.76  fof(f135,plain,(
% 2.94/0.76    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f134,f50])).
% 2.94/0.76  fof(f134,plain,(
% 2.94/0.76    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f133,f51])).
% 2.94/0.76  fof(f133,plain,(
% 2.94/0.76    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f130,f52])).
% 2.94/0.76  fof(f130,plain,(
% 2.94/0.76    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.94/0.76    inference(resolution,[],[f74,f57])).
% 2.94/0.76  fof(f395,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f394,f53])).
% 2.94/0.76  fof(f394,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f393,f54])).
% 2.94/0.76  fof(f393,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f392,f55])).
% 2.94/0.76  fof(f392,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f391,f60])).
% 2.94/0.76  fof(f391,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f390,f61])).
% 2.94/0.76  fof(f390,plain,(
% 2.94/0.76    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(resolution,[],[f159,f62])).
% 2.94/0.76  fof(f159,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f156,f108])).
% 2.94/0.76  fof(f108,plain,(
% 2.94/0.76    ( ! [X0] : (~m1_pre_topc(sK0,X0) | m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.94/0.76    inference(resolution,[],[f78,f57])).
% 2.94/0.76  fof(f156,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(resolution,[],[f72,f57])).
% 2.94/0.76  fof(f239,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 2.94/0.76    inference(subsumption_resolution,[],[f238,f50])).
% 2.94/0.76  fof(f238,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f237,f51])).
% 2.94/0.76  fof(f237,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f236,f52])).
% 2.94/0.76  fof(f236,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f231,f94])).
% 2.94/0.76  fof(f231,plain,(
% 2.94/0.76    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f129,f57])).
% 2.94/0.76  fof(f1486,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    inference(subsumption_resolution,[],[f1485,f738])).
% 2.94/0.76  fof(f738,plain,(
% 2.94/0.76    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.94/0.76    inference(superposition,[],[f280,f553])).
% 2.94/0.76  fof(f280,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.94/0.76    inference(subsumption_resolution,[],[f279,f50])).
% 2.94/0.76  fof(f279,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f278,f51])).
% 2.94/0.76  fof(f278,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f277,f52])).
% 2.94/0.76  fof(f277,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f272,f94])).
% 2.94/0.76  fof(f272,plain,(
% 2.94/0.76    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f147,f57])).
% 2.94/0.76  fof(f1485,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    inference(subsumption_resolution,[],[f1484,f737])).
% 2.94/0.76  fof(f737,plain,(
% 2.94/0.76    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.94/0.76    inference(superposition,[],[f297,f553])).
% 2.94/0.76  fof(f297,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.94/0.76    inference(subsumption_resolution,[],[f296,f50])).
% 2.94/0.76  fof(f296,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f295,f51])).
% 2.94/0.76  fof(f295,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f294,f52])).
% 2.94/0.76  fof(f294,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f289,f94])).
% 2.94/0.76  fof(f289,plain,(
% 2.94/0.76    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f153,f57])).
% 2.94/0.76  fof(f1484,plain,(
% 2.94/0.76    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 2.94/0.76    inference(resolution,[],[f666,f82])).
% 2.94/0.76  fof(f82,plain,(
% 2.94/0.76    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.94/0.76    inference(cnf_transformation,[],[f49])).
% 2.94/0.76  fof(f49,plain,(
% 2.94/0.76    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/0.76    inference(nnf_transformation,[],[f38])).
% 2.94/0.76  fof(f38,plain,(
% 2.94/0.76    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.94/0.76    inference(flattening,[],[f37])).
% 2.94/0.76  fof(f37,plain,(
% 2.94/0.76    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.94/0.76    inference(ennf_transformation,[],[f1])).
% 2.94/0.76  fof(f1,axiom,(
% 2.94/0.76    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.94/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 2.94/0.76  fof(f666,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 2.94/0.76    inference(forward_demodulation,[],[f665,f557])).
% 2.94/0.76  fof(f665,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 2.94/0.76    inference(forward_demodulation,[],[f664,f553])).
% 2.94/0.76  fof(f664,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 2.94/0.76    inference(subsumption_resolution,[],[f663,f50])).
% 2.94/0.76  fof(f663,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f662,f51])).
% 2.94/0.76  fof(f662,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(subsumption_resolution,[],[f661,f52])).
% 2.94/0.76  fof(f661,plain,(
% 2.94/0.76    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 2.94/0.76    inference(resolution,[],[f389,f94])).
% 2.94/0.76  fof(f389,plain,(
% 2.94/0.76    ( ! [X5] : (~m1_pre_topc(sK0,X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f388,f58])).
% 2.94/0.76  fof(f388,plain,(
% 2.94/0.76    ( ! [X5] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4)) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f387,f56])).
% 2.94/0.76  fof(f387,plain,(
% 2.94/0.76    ( ! [X5] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4)) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f364,f59])).
% 2.94/0.76  fof(f364,plain,(
% 2.94/0.76    ( ! [X5] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X5,sK1,sK3,sK2,k3_tmap_1(X5,sK1,sK0,sK3,sK4)),k3_tmap_1(X5,sK1,sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 2.94/0.76    inference(resolution,[],[f194,f63])).
% 2.94/0.76  fof(f194,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f193,f78])).
% 2.94/0.76  fof(f193,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f192,f78])).
% 2.94/0.76  fof(f192,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f191,f53])).
% 2.94/0.76  fof(f191,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f190,f54])).
% 2.94/0.76  fof(f190,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f189,f55])).
% 2.94/0.76  fof(f189,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f188,f50])).
% 2.94/0.76  fof(f188,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f187,f60])).
% 2.94/0.76  fof(f187,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f186,f61])).
% 2.94/0.76  fof(f186,plain,(
% 2.94/0.76    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 2.94/0.76    inference(resolution,[],[f73,f62])).
% 2.94/0.76  fof(f73,plain,(
% 2.94/0.76    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.76    inference(cnf_transformation,[],[f24])).
% 2.94/0.76  fof(f24,plain,(
% 2.94/0.76    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/0.76    inference(flattening,[],[f23])).
% 2.94/0.76  fof(f23,plain,(
% 2.94/0.76    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/0.76    inference(ennf_transformation,[],[f12])).
% 2.94/0.76  fof(f12,axiom,(
% 2.94/0.76    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 2.94/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).
% 2.94/0.76  fof(f748,plain,(
% 2.94/0.76    spl7_1),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f747])).
% 2.94/0.76  fof(f747,plain,(
% 2.94/0.76    $false | spl7_1),
% 2.94/0.76    inference(subsumption_resolution,[],[f742,f173])).
% 2.94/0.76  fof(f173,plain,(
% 2.94/0.76    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | spl7_1),
% 2.94/0.76    inference(avatar_component_clause,[],[f171])).
% 2.94/0.76  fof(f171,plain,(
% 2.94/0.76    spl7_1 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.94/0.76  fof(f742,plain,(
% 2.94/0.76    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 2.94/0.76    inference(superposition,[],[f243,f557])).
% 2.94/0.76  fof(f746,plain,(
% 2.94/0.76    spl7_2),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f745])).
% 2.94/0.76  fof(f745,plain,(
% 2.94/0.76    $false | spl7_2),
% 2.94/0.76    inference(subsumption_resolution,[],[f741,f177])).
% 2.94/0.76  fof(f177,plain,(
% 2.94/0.76    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_2),
% 2.94/0.76    inference(avatar_component_clause,[],[f175])).
% 2.94/0.76  fof(f175,plain,(
% 2.94/0.76    spl7_2 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.94/0.76  fof(f741,plain,(
% 2.94/0.76    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.94/0.76    inference(superposition,[],[f284,f557])).
% 2.94/0.76  fof(f744,plain,(
% 2.94/0.76    spl7_3),
% 2.94/0.76    inference(avatar_contradiction_clause,[],[f743])).
% 2.94/0.76  fof(f743,plain,(
% 2.94/0.76    $false | spl7_3),
% 2.94/0.76    inference(subsumption_resolution,[],[f740,f181])).
% 2.94/0.76  fof(f181,plain,(
% 2.94/0.76    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_3),
% 2.94/0.76    inference(avatar_component_clause,[],[f179])).
% 2.94/0.76  fof(f179,plain,(
% 2.94/0.76    spl7_3 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.94/0.76    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.94/0.76  fof(f740,plain,(
% 2.94/0.76    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.94/0.76    inference(superposition,[],[f301,f557])).
% 2.94/0.76  fof(f185,plain,(
% 2.94/0.76    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4),
% 2.94/0.76    inference(avatar_split_clause,[],[f169,f183,f179,f175,f171])).
% 2.94/0.76  fof(f169,plain,(
% 2.94/0.76    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f168,f53])).
% 2.94/0.76  fof(f168,plain,(
% 2.94/0.76    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | v2_struct_0(sK1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f167,f54])).
% 2.94/0.76  fof(f167,plain,(
% 2.94/0.76    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.76    inference(subsumption_resolution,[],[f166,f55])).
% 2.94/0.77  fof(f166,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f165,f58])).
% 2.94/0.77  fof(f165,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f164,f107])).
% 2.94/0.77  fof(f164,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f163,f100])).
% 2.94/0.77  fof(f163,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.77    inference(subsumption_resolution,[],[f162,f64])).
% 2.94/0.77  fof(f64,plain,(
% 2.94/0.77    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.94/0.77    inference(cnf_transformation,[],[f48])).
% 2.94/0.77  fof(f162,plain,(
% 2.94/0.77    ( ! [X0] : (r1_tmap_1(X0,sK1,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X0),sK5) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 2.94/0.77    inference(resolution,[],[f87,f67])).
% 2.94/0.77  fof(f67,plain,(
% 2.94/0.77    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 2.94/0.77    inference(cnf_transformation,[],[f48])).
% 2.94/0.77  fof(f87,plain,(
% 2.94/0.77    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.77    inference(equality_resolution,[],[f75])).
% 2.94/0.77  fof(f75,plain,(
% 2.94/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.94/0.77    inference(cnf_transformation,[],[f28])).
% 2.94/0.77  fof(f28,plain,(
% 2.94/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.94/0.77    inference(flattening,[],[f27])).
% 2.94/0.77  fof(f27,plain,(
% 2.94/0.77    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.94/0.77    inference(ennf_transformation,[],[f11])).
% 2.94/0.77  fof(f11,axiom,(
% 2.94/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.94/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 2.94/0.77  % SZS output end Proof for theBenchmark
% 2.94/0.77  % (23761)------------------------------
% 2.94/0.77  % (23761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.77  % (23761)Termination reason: Refutation
% 2.94/0.77  
% 2.94/0.77  % (23761)Memory used [KB]: 11769
% 2.94/0.77  % (23761)Time elapsed: 0.313 s
% 2.94/0.77  % (23761)------------------------------
% 2.94/0.77  % (23761)------------------------------
% 2.94/0.77  % (23750)Success in time 0.396 s
%------------------------------------------------------------------------------
