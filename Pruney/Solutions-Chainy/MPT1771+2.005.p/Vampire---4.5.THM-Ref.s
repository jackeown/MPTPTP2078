%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  266 (6880 expanded)
%              Number of leaves         :   20 (3788 expanded)
%              Depth                    :   35
%              Number of atoms          : 1778 (121346 expanded)
%              Number of equality atoms :   91 (9138 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1099,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f474,f476,f478,f1098])).

fof(f1098,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f1097])).

fof(f1097,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f1096,f71])).

fof(f71,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f34,f33,f32,f31,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f55,plain,(
    ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f1096,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ spl7_7 ),
    inference(superposition,[],[f496,f829])).

fof(f829,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(subsumption_resolution,[],[f828,f642])).

fof(f642,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(forward_demodulation,[],[f641,f420])).

fof(f420,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) ),
    inference(subsumption_resolution,[],[f419,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f419,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f418,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f418,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f417,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f417,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f292,f72])).

fof(f72,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f292,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f291,f251])).

fof(f251,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f250,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f250,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f249,f41])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f249,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f248,f42])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f248,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f247,f47])).

fof(f47,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f247,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f246,f48])).

fof(f48,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f246,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f96,f49])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X2,X3] :
      ( k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,(
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
    inference(subsumption_resolution,[],[f88,f39])).

fof(f88,plain,(
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
    inference(resolution,[],[f60,f46])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f291,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f290,f40])).

fof(f290,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f289,f41])).

fof(f289,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f288,f42])).

fof(f288,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f287,f47])).

fof(f287,plain,(
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
    inference(subsumption_resolution,[],[f286,f48])).

fof(f286,plain,(
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
    inference(resolution,[],[f131,f49])).

fof(f131,plain,(
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
    inference(subsumption_resolution,[],[f126,f75])).

fof(f75,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK0,X1)
      | m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f126,plain,(
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
    inference(resolution,[],[f57,f46])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f641,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) ),
    inference(subsumption_resolution,[],[f640,f37])).

fof(f640,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f639,f38])).

fof(f639,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f638,f39])).

fof(f638,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f633,f46])).

fof(f633,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f356,f44])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f356,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(X9,X8)
      | v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(sK3,X8)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f355,f40])).

fof(f355,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f354,f41])).

fof(f354,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))
      | ~ m1_pre_topc(X9,X8)
      | ~ m1_pre_topc(sK3,X8)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(subsumption_resolution,[],[f353,f42])).

fof(f353,plain,(
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
    inference(subsumption_resolution,[],[f352,f189])).

fof(f189,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f188,f37])).

fof(f188,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f187,f38])).

fof(f187,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f186,f39])).

fof(f186,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f72])).

fof(f178,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f84,f40])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f83,f41])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,(
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
    inference(subsumption_resolution,[],[f81,f47])).

fof(f81,plain,(
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
    inference(subsumption_resolution,[],[f80,f48])).

fof(f80,plain,(
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
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f352,plain,(
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
    inference(subsumption_resolution,[],[f327,f218])).

fof(f218,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f217,f37])).

fof(f217,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f216,f38])).

fof(f216,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f215,f39])).

fof(f215,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f72])).

fof(f207,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,(
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
    inference(subsumption_resolution,[],[f114,f47])).

fof(f114,plain,(
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
    inference(subsumption_resolution,[],[f113,f48])).

fof(f113,plain,(
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
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f327,plain,(
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
    inference(resolution,[],[f235,f64])).

fof(f235,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f234,f37])).

fof(f234,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f38])).

fof(f233,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f232,f39])).

fof(f232,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f72])).

fof(f224,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f124,f46])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f40])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f121,f42])).

fof(f121,plain,(
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
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,(
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
    inference(subsumption_resolution,[],[f119,f48])).

fof(f119,plain,(
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
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f828,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f827,f733])).

fof(f733,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f732,f420])).

fof(f732,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f731,f37])).

fof(f731,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f730,f38])).

fof(f730,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f729,f39])).

fof(f729,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f724,f46])).

fof(f724,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f351,f44])).

fof(f351,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X7,X6)
      | v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f350,f40])).

fof(f350,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f349,f41])).

fof(f349,plain,(
    ! [X6,X7] :
      ( v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1))
      | ~ m1_pre_topc(X7,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f348,f42])).

fof(f348,plain,(
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
    inference(subsumption_resolution,[],[f347,f189])).

fof(f347,plain,(
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
    inference(subsumption_resolution,[],[f326,f218])).

fof(f326,plain,(
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
    inference(resolution,[],[f235,f65])).

fof(f827,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f826,f811])).

fof(f811,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f810,f420])).

fof(f810,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f809,f37])).

fof(f809,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f808,f38])).

fof(f808,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f807,f39])).

fof(f807,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f802,f46])).

fof(f802,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f346,f44])).

fof(f346,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X5,X4)
      | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(sK3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f345,f40])).

fof(f345,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f344,f41])).

fof(f344,plain,(
    ! [X4,X5] :
      ( m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X5,X4)
      | ~ m1_pre_topc(sK3,X4)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f343,f42])).

fof(f343,plain,(
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
    inference(subsumption_resolution,[],[f342,f189])).

fof(f342,plain,(
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
    inference(subsumption_resolution,[],[f325,f218])).

fof(f325,plain,(
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
    inference(resolution,[],[f235,f66])).

fof(f826,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f825,f423])).

fof(f423,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(superposition,[],[f185,f416])).

fof(f416,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f415,f37])).

fof(f415,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f414,f38])).

fof(f414,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f413,f39])).

fof(f413,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f285,f72])).

fof(f285,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f284,f245])).

fof(f245,plain,(
    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f244,f40])).

fof(f244,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f243,f41])).

fof(f243,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f242,f42])).

fof(f242,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f241,f47])).

fof(f241,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f240,f48])).

fof(f240,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f93,f49])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,(
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
    inference(subsumption_resolution,[],[f87,f39])).

fof(f87,plain,(
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
    inference(resolution,[],[f60,f44])).

fof(f284,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f283,f40])).

fof(f283,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f282,f41])).

fof(f282,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f281,f42])).

fof(f281,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f280,plain,(
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
    inference(subsumption_resolution,[],[f279,f48])).

fof(f279,plain,(
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
    inference(resolution,[],[f130,f49])).

fof(f130,plain,(
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
    inference(subsumption_resolution,[],[f125,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f61,f44])).

fof(f125,plain,(
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
    inference(resolution,[],[f57,f44])).

fof(f185,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f184,f37])).

fof(f184,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f38])).

fof(f183,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f39])).

fof(f182,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f72])).

fof(f177,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f85,f44])).

fof(f825,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f824,f422])).

fof(f422,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f214,f416])).

fof(f214,plain,(
    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f213,f37])).

fof(f213,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f212,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f39])).

fof(f211,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f72])).

fof(f206,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f118,f44])).

fof(f824,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(subsumption_resolution,[],[f528,f421])).

fof(f421,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f231,f416])).

fof(f231,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f230,f37])).

fof(f230,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f38])).

fof(f229,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f39])).

fof(f228,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f72])).

fof(f223,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f124,f44])).

fof(f528,plain,
    ( k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(resolution,[],[f443,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f443,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f442,f420])).

fof(f442,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(forward_demodulation,[],[f441,f416])).

fof(f441,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f440,f37])).

fof(f440,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f439,f38])).

fof(f439,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f438,f39])).

fof(f438,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f269,f72])).

fof(f269,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(sK0,X3)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f268,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f268,plain,(
    ! [X3] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f267,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f267,plain,(
    ! [X3] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4))
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f255,f46])).

fof(f255,plain,(
    ! [X3] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK0,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f164,f50])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f164,plain,(
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
    inference(subsumption_resolution,[],[f163,f61])).

fof(f163,plain,(
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
    inference(subsumption_resolution,[],[f162,f61])).

fof(f162,plain,(
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
    inference(subsumption_resolution,[],[f161,f40])).

fof(f161,plain,(
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
    inference(subsumption_resolution,[],[f160,f41])).

fof(f160,plain,(
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
    inference(subsumption_resolution,[],[f159,f42])).

fof(f159,plain,(
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
    inference(subsumption_resolution,[],[f158,f37])).

fof(f158,plain,(
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
    inference(subsumption_resolution,[],[f157,f47])).

fof(f157,plain,(
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
    inference(subsumption_resolution,[],[f156,f48])).

fof(f156,plain,(
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
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f496,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f495,f50])).

fof(f495,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f484,f43])).

fof(f484,plain,
    ( v2_struct_0(sK2)
    | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f482,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f52,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f481,f39])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f480,f38])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f479,f37])).

fof(f479,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_7 ),
    inference(resolution,[],[f154,f46])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f478,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f472,f143])).

fof(f143,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl7_4
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f472,plain,(
    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(superposition,[],[f189,f420])).

fof(f476,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f471,f147])).

fof(f147,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_5
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f471,plain,(
    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(superposition,[],[f218,f420])).

fof(f474,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f470,f151])).

fof(f151,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_6
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f470,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f235,f420])).

fof(f155,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f139,f153,f149,f145,f141])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f138,f61])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f136,f41])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f135,f42])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f134,f45])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f51,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,X4,X6)
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (30306)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (30297)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (30315)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (30301)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (30319)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (30311)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (30303)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (30300)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (30299)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (30312)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (30305)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (30308)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (30307)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (30296)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (30298)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (30321)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (30318)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (30302)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (30310)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (30304)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (30314)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (30320)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (30306)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (30316)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (30317)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (30309)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.48/0.55  % (30313)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.48/0.55  % SZS output start Proof for theBenchmark
% 1.48/0.55  fof(f1099,plain,(
% 1.48/0.55    $false),
% 1.48/0.55    inference(avatar_sat_refutation,[],[f155,f474,f476,f478,f1098])).
% 1.48/0.55  fof(f1098,plain,(
% 1.48/0.55    ~spl7_7),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f1097])).
% 1.48/0.55  fof(f1097,plain,(
% 1.48/0.55    $false | ~spl7_7),
% 1.48/0.55    inference(subsumption_resolution,[],[f1096,f71])).
% 1.48/0.55  fof(f71,plain,(
% 1.48/0.55    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5)),
% 1.48/0.55    inference(superposition,[],[f55,f53])).
% 1.48/0.55  fof(f53,plain,(
% 1.48/0.55    sK5 = sK6),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ((((((~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.48/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f12,f34,f33,f32,f31,f30,f29,f28])).
% 1.48/0.55  fof(f28,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f29,plain,(
% 1.48/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(sK0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(sK0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f30,plain,(
% 1.48/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK1,k2_tmap_1(sK0,sK1,X4,X2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f31,plain,(
% 1.48/0.55    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(X3,sK1,k2_tmap_1(sK0,sK1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f32,plain,(
% 1.48/0.55    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,X4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,X4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    ? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f34,plain,(
% 1.48/0.55    ? [X6] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),X6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6) & r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.48/0.55    introduced(choice_axiom,[])).
% 1.48/0.55  fof(f12,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.48/0.55    inference(flattening,[],[f11])).
% 1.48/0.55  fof(f11,plain,(
% 1.48/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6) & (r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f10])).
% 1.48/0.55  fof(f10,negated_conjecture,(
% 1.48/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 1.48/0.55    inference(negated_conjecture,[],[f9])).
% 1.48/0.55  fof(f9,conjecture,(
% 1.48/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X3,X1,k2_tmap_1(X0,X1,X4,X3),X5) & X5 = X6) => r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,X4,X2),X6))))))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).
% 1.48/0.55  fof(f55,plain,(
% 1.48/0.55    ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK6)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f1096,plain,(
% 1.48/0.55    r1_tmap_1(sK2,sK1,k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~spl7_7),
% 1.48/0.55    inference(superposition,[],[f496,f829])).
% 1.48/0.55  fof(f829,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.48/0.55    inference(subsumption_resolution,[],[f828,f642])).
% 1.48/0.55  fof(f642,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.55    inference(forward_demodulation,[],[f641,f420])).
% 1.48/0.55  fof(f420,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),
% 1.48/0.55    inference(subsumption_resolution,[],[f419,f37])).
% 1.48/0.55  fof(f37,plain,(
% 1.48/0.55    ~v2_struct_0(sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f419,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f418,f38])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    v2_pre_topc(sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f418,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f417,f39])).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    l1_pre_topc(sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f417,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f292,f72])).
% 1.48/0.55  fof(f72,plain,(
% 1.48/0.55    m1_pre_topc(sK0,sK0)),
% 1.48/0.55    inference(resolution,[],[f56,f39])).
% 1.48/0.55  fof(f56,plain,(
% 1.48/0.55    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f13])).
% 1.48/0.55  fof(f13,plain,(
% 1.48/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.48/0.55    inference(ennf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.48/0.55  fof(f292,plain,(
% 1.48/0.55    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK3) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f291,f251])).
% 1.48/0.55  fof(f251,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3))),
% 1.48/0.55    inference(subsumption_resolution,[],[f250,f40])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ~v2_struct_0(sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f250,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | v2_struct_0(sK1)),
% 1.48/0.55    inference(subsumption_resolution,[],[f249,f41])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    v2_pre_topc(sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f249,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.55    inference(subsumption_resolution,[],[f248,f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    l1_pre_topc(sK1)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f248,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.55    inference(subsumption_resolution,[],[f247,f47])).
% 1.48/0.55  fof(f47,plain,(
% 1.48/0.55    v1_funct_1(sK4)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f247,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.55    inference(subsumption_resolution,[],[f246,f48])).
% 1.48/0.55  fof(f48,plain,(
% 1.48/0.55    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f246,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.55    inference(resolution,[],[f96,f49])).
% 1.48/0.55  fof(f49,plain,(
% 1.48/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f96,plain,(
% 1.48/0.55    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f95,f37])).
% 1.48/0.55  fof(f95,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f94,f38])).
% 1.48/0.55  fof(f94,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f88,f39])).
% 1.48/0.55  fof(f88,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k2_tmap_1(sK0,X2,X3,sK3) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X3,u1_struct_0(sK3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.55    inference(resolution,[],[f60,f46])).
% 1.48/0.55  fof(f46,plain,(
% 1.48/0.55    m1_pre_topc(sK3,sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f60,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f21])).
% 1.48/0.55  fof(f21,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.55    inference(flattening,[],[f20])).
% 1.48/0.55  fof(f20,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f2])).
% 1.48/0.55  fof(f2,axiom,(
% 1.48/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.48/0.55  fof(f291,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f290,f40])).
% 1.48/0.55  fof(f290,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f289,f41])).
% 1.48/0.55  fof(f289,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f288,f42])).
% 1.48/0.55  fof(f288,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f287,f47])).
% 1.48/0.55  fof(f287,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f286,f48])).
% 1.48/0.55  fof(f286,plain,(
% 1.48/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(X0,sK1,sK0,sK3,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(resolution,[],[f131,f49])).
% 1.48/0.55  fof(f131,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f126,f75])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    ( ! [X1] : (~m1_pre_topc(sK0,X1) | m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 1.48/0.55    inference(resolution,[],[f61,f46])).
% 1.48/0.55  fof(f61,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f23])).
% 1.48/0.55  fof(f23,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.55    inference(flattening,[],[f22])).
% 1.48/0.55  fof(f22,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.48/0.55  fof(f126,plain,(
% 1.48/0.55    ( ! [X4,X5,X3] : (k3_tmap_1(X3,X4,sK0,sK3,X5) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X4),X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.48/0.55    inference(resolution,[],[f57,f46])).
% 1.48/0.55  fof(f57,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f15])).
% 1.48/0.55  fof(f15,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.55    inference(flattening,[],[f14])).
% 1.48/0.55  fof(f14,plain,(
% 1.48/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f3])).
% 1.48/0.55  fof(f3,axiom,(
% 1.48/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.48/0.55  fof(f641,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)))),
% 1.48/0.55    inference(subsumption_resolution,[],[f640,f37])).
% 1.48/0.55  fof(f640,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f639,f38])).
% 1.48/0.55  fof(f639,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f638,f39])).
% 1.48/0.55  fof(f638,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f633,f46])).
% 1.48/0.55  fof(f633,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f356,f44])).
% 1.48/0.55  fof(f44,plain,(
% 1.48/0.55    m1_pre_topc(sK2,sK0)),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f356,plain,(
% 1.48/0.55    ( ! [X8,X9] : (~m1_pre_topc(X9,X8) | v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f355,f40])).
% 1.48/0.55  fof(f355,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f354,f41])).
% 1.48/0.55  fof(f354,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f353,f42])).
% 1.48/0.55  fof(f353,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f352,f189])).
% 1.48/0.55  fof(f189,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4))),
% 1.48/0.55    inference(subsumption_resolution,[],[f188,f37])).
% 1.48/0.55  fof(f188,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f187,f38])).
% 1.48/0.55  fof(f187,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f186,f39])).
% 1.48/0.55  fof(f186,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f178,f72])).
% 1.48/0.55  fof(f178,plain,(
% 1.48/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f85,f46])).
% 1.48/0.55  fof(f85,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f84,f40])).
% 1.48/0.55  fof(f84,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f83,f41])).
% 1.48/0.55  fof(f83,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f82,f42])).
% 1.48/0.55  fof(f82,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f81,f47])).
% 1.48/0.55  fof(f81,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f80,f48])).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK0,X1,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(resolution,[],[f64,f49])).
% 1.48/0.55  fof(f64,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f27,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.48/0.55    inference(flattening,[],[f26])).
% 1.48/0.55  fof(f26,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.48/0.55  fof(f352,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f327,f218])).
% 1.48/0.55  fof(f218,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.48/0.55    inference(subsumption_resolution,[],[f217,f37])).
% 1.48/0.55  fof(f217,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f216,f38])).
% 1.48/0.55  fof(f216,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f215,f39])).
% 1.48/0.55  fof(f215,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f207,f72])).
% 1.48/0.55  fof(f207,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f118,f46])).
% 1.48/0.55  fof(f118,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f117,f40])).
% 1.48/0.55  fof(f117,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f116,f41])).
% 1.48/0.55  fof(f116,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f115,f42])).
% 1.48/0.55  fof(f115,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f114,f47])).
% 1.48/0.55  fof(f114,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f113,f48])).
% 1.48/0.55  fof(f113,plain,(
% 1.48/0.55    ( ! [X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK1,sK0,X1,sK4),u1_struct_0(X1),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(resolution,[],[f65,f49])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f327,plain,(
% 1.48/0.55    ( ! [X8,X9] : (v1_funct_1(k3_tmap_1(X8,sK1,sK3,X9,k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X9,X8) | ~m1_pre_topc(sK3,X8) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8) | v2_struct_0(X8)) )),
% 1.48/0.55    inference(resolution,[],[f235,f64])).
% 1.48/0.55  fof(f235,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.48/0.55    inference(subsumption_resolution,[],[f234,f37])).
% 1.48/0.55  fof(f234,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f233,f38])).
% 1.48/0.55  fof(f233,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f232,f39])).
% 1.48/0.55  fof(f232,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f224,f72])).
% 1.48/0.55  fof(f224,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f124,f46])).
% 1.48/0.55  fof(f124,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f123,f40])).
% 1.48/0.55  fof(f123,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f122,f41])).
% 1.48/0.55  fof(f122,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f121,f42])).
% 1.48/0.55  fof(f121,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f120,f47])).
% 1.48/0.55  fof(f120,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f119,f48])).
% 1.48/0.55  fof(f119,plain,(
% 1.48/0.55    ( ! [X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK1,sK0,X1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(resolution,[],[f66,f49])).
% 1.48/0.55  fof(f66,plain,(
% 1.48/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f27])).
% 1.48/0.55  fof(f828,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.55    inference(subsumption_resolution,[],[f827,f733])).
% 1.48/0.55  fof(f733,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.48/0.55    inference(forward_demodulation,[],[f732,f420])).
% 1.48/0.55  fof(f732,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.48/0.55    inference(subsumption_resolution,[],[f731,f37])).
% 1.48/0.55  fof(f731,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f730,f38])).
% 1.48/0.55  fof(f730,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f729,f39])).
% 1.48/0.55  fof(f729,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f724,f46])).
% 1.48/0.55  fof(f724,plain,(
% 1.48/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f351,f44])).
% 1.48/0.55  fof(f351,plain,(
% 1.48/0.55    ( ! [X6,X7] : (~m1_pre_topc(X7,X6) | v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f350,f40])).
% 1.48/0.55  fof(f350,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f349,f41])).
% 1.48/0.55  fof(f349,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f348,f42])).
% 1.48/0.55  fof(f348,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f347,f189])).
% 1.48/0.55  fof(f347,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f326,f218])).
% 1.48/0.55  fof(f326,plain,(
% 1.48/0.55    ( ! [X6,X7] : (v1_funct_2(k3_tmap_1(X6,sK1,sK3,X7,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(X7),u1_struct_0(sK1)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X7,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.48/0.55    inference(resolution,[],[f235,f65])).
% 1.48/0.55  fof(f827,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.55    inference(subsumption_resolution,[],[f826,f811])).
% 1.48/0.55  fof(f811,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.55    inference(forward_demodulation,[],[f810,f420])).
% 1.48/0.55  fof(f810,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.55    inference(subsumption_resolution,[],[f809,f37])).
% 1.48/0.55  fof(f809,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f808,f38])).
% 1.48/0.55  fof(f808,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f807,f39])).
% 1.48/0.55  fof(f807,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f802,f46])).
% 1.48/0.55  fof(f802,plain,(
% 1.48/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f346,f44])).
% 1.48/0.55  fof(f346,plain,(
% 1.48/0.55    ( ! [X4,X5] : (~m1_pre_topc(X5,X4) | m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f345,f40])).
% 1.48/0.55  fof(f345,plain,(
% 1.48/0.55    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f344,f41])).
% 1.48/0.55  fof(f344,plain,(
% 1.48/0.55    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f343,f42])).
% 1.48/0.55  fof(f343,plain,(
% 1.48/0.55    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f342,f189])).
% 1.48/0.55  fof(f342,plain,(
% 1.48/0.55    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(subsumption_resolution,[],[f325,f218])).
% 1.48/0.55  fof(f325,plain,(
% 1.48/0.55    ( ! [X4,X5] : (m1_subset_1(k3_tmap_1(X4,sK1,sK3,X5,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) | ~m1_pre_topc(X5,X4) | ~m1_pre_topc(sK3,X4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 1.48/0.55    inference(resolution,[],[f235,f66])).
% 1.48/0.55  fof(f826,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.55    inference(subsumption_resolution,[],[f825,f423])).
% 1.48/0.55  fof(f423,plain,(
% 1.48/0.55    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.48/0.55    inference(superposition,[],[f185,f416])).
% 1.48/0.55  fof(f416,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)),
% 1.48/0.55    inference(subsumption_resolution,[],[f415,f37])).
% 1.48/0.55  fof(f415,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f414,f38])).
% 1.48/0.55  fof(f414,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(subsumption_resolution,[],[f413,f39])).
% 1.48/0.55  fof(f413,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.55    inference(resolution,[],[f285,f72])).
% 1.48/0.55  fof(f285,plain,(
% 1.48/0.55    ( ! [X0] : (~m1_pre_topc(sK0,X0) | k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f284,f245])).
% 1.48/0.55  fof(f245,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.48/0.55    inference(subsumption_resolution,[],[f244,f40])).
% 1.48/0.55  fof(f244,plain,(
% 1.48/0.55    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | v2_struct_0(sK1)),
% 1.48/0.55    inference(subsumption_resolution,[],[f243,f41])).
% 1.48/0.56  fof(f243,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f242,f42])).
% 1.48/0.56  fof(f242,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f241,f47])).
% 1.48/0.56  fof(f241,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.56    inference(subsumption_resolution,[],[f240,f48])).
% 1.48/0.56  fof(f240,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)),
% 1.48/0.56    inference(resolution,[],[f93,f49])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f92,f37])).
% 1.48/0.56  fof(f92,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f91,f38])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f87,f39])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_tmap_1(sK0,X0,X1,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.48/0.56    inference(resolution,[],[f60,f44])).
% 1.48/0.56  fof(f284,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f283,f40])).
% 1.48/0.56  fof(f283,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f282,f41])).
% 1.48/0.56  fof(f282,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f281,f42])).
% 1.48/0.56  fof(f281,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f280,f47])).
% 1.48/0.56  fof(f280,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f279,f48])).
% 1.48/0.56  fof(f279,plain,(
% 1.48/0.56    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0,sK1,sK0,sK2,sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(resolution,[],[f130,f49])).
% 1.48/0.56  fof(f130,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f125,f74])).
% 1.48/0.56  fof(f74,plain,(
% 1.48/0.56    ( ! [X0] : (~m1_pre_topc(sK0,X0) | m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.56    inference(resolution,[],[f61,f44])).
% 1.48/0.56  fof(f125,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k3_tmap_1(X0,X1,sK0,sK2,X2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X2,u1_struct_0(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.48/0.56    inference(resolution,[],[f57,f44])).
% 1.48/0.56  fof(f185,plain,(
% 1.48/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.48/0.56    inference(subsumption_resolution,[],[f184,f37])).
% 1.48/0.56  fof(f184,plain,(
% 1.48/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f183,f38])).
% 1.48/0.56  fof(f183,plain,(
% 1.48/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f182,f39])).
% 1.48/0.56  fof(f182,plain,(
% 1.48/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f177,f72])).
% 1.48/0.56  fof(f177,plain,(
% 1.48/0.56    v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(resolution,[],[f85,f44])).
% 1.48/0.56  fof(f825,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.56    inference(subsumption_resolution,[],[f824,f422])).
% 1.48/0.56  fof(f422,plain,(
% 1.48/0.56    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.48/0.56    inference(superposition,[],[f214,f416])).
% 1.48/0.56  fof(f214,plain,(
% 1.48/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.48/0.56    inference(subsumption_resolution,[],[f213,f37])).
% 1.48/0.56  fof(f213,plain,(
% 1.48/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f212,f38])).
% 1.48/0.56  fof(f212,plain,(
% 1.48/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f211,f39])).
% 1.48/0.56  fof(f211,plain,(
% 1.48/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f206,f72])).
% 1.48/0.56  fof(f206,plain,(
% 1.48/0.56    v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(resolution,[],[f118,f44])).
% 1.48/0.56  fof(f824,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.56    inference(subsumption_resolution,[],[f528,f421])).
% 1.48/0.56  fof(f421,plain,(
% 1.48/0.56    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.56    inference(superposition,[],[f231,f416])).
% 1.48/0.56  fof(f231,plain,(
% 1.48/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.48/0.56    inference(subsumption_resolution,[],[f230,f37])).
% 1.48/0.56  fof(f230,plain,(
% 1.48/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f229,f38])).
% 1.48/0.56  fof(f229,plain,(
% 1.48/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f228,f39])).
% 1.48/0.56  fof(f228,plain,(
% 1.48/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(subsumption_resolution,[],[f223,f72])).
% 1.48/0.56  fof(f223,plain,(
% 1.48/0.56    m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.48/0.56    inference(resolution,[],[f124,f44])).
% 1.48/0.56  fof(f528,plain,(
% 1.48/0.56    k2_tmap_1(sK0,sK1,sK4,sK2) = k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) | ~m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 1.48/0.56    inference(resolution,[],[f443,f62])).
% 1.48/0.56  fof(f62,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.56    inference(nnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.56    inference(flattening,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.56    inference(ennf_transformation,[],[f1])).
% 1.62/0.56  fof(f1,axiom,(
% 1.62/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.62/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.62/0.56  fof(f443,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.62/0.56    inference(forward_demodulation,[],[f442,f420])).
% 1.62/0.56  fof(f442,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k2_tmap_1(sK0,sK1,sK4,sK2))),
% 1.62/0.56    inference(forward_demodulation,[],[f441,f416])).
% 1.62/0.56  fof(f441,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4))),
% 1.62/0.56    inference(subsumption_resolution,[],[f440,f37])).
% 1.62/0.56  fof(f440,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f439,f38])).
% 1.62/0.56  fof(f439,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(subsumption_resolution,[],[f438,f39])).
% 1.62/0.56  fof(f438,plain,(
% 1.62/0.56    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.62/0.56    inference(resolution,[],[f269,f72])).
% 1.62/0.56  fof(f269,plain,(
% 1.62/0.56    ( ! [X3] : (~m1_pre_topc(sK0,X3) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f268,f45])).
% 1.62/0.56  fof(f45,plain,(
% 1.62/0.56    ~v2_struct_0(sK3)),
% 1.62/0.56    inference(cnf_transformation,[],[f35])).
% 1.62/0.56  fof(f268,plain,(
% 1.62/0.56    ( ! [X3] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4)) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f267,f43])).
% 1.62/0.56  fof(f43,plain,(
% 1.62/0.56    ~v2_struct_0(sK2)),
% 1.62/0.56    inference(cnf_transformation,[],[f35])).
% 1.62/0.56  fof(f267,plain,(
% 1.62/0.56    ( ! [X3] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4)) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f255,f46])).
% 1.62/0.56  fof(f255,plain,(
% 1.62/0.56    ( ! [X3] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(X3,sK1,sK3,sK2,k3_tmap_1(X3,sK1,sK0,sK3,sK4)),k3_tmap_1(X3,sK1,sK0,sK2,sK4)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK0,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 1.62/0.56    inference(resolution,[],[f164,f50])).
% 1.62/0.56  fof(f50,plain,(
% 1.62/0.56    m1_pre_topc(sK2,sK3)),
% 1.62/0.56    inference(cnf_transformation,[],[f35])).
% 1.62/0.56  fof(f164,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X2) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f163,f61])).
% 1.62/0.56  fof(f163,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f162,f61])).
% 1.62/0.56  fof(f162,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f161,f40])).
% 1.62/0.56  fof(f161,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f160,f41])).
% 1.62/0.56  fof(f160,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f159,f42])).
% 1.62/0.56  fof(f159,plain,(
% 1.62/0.56    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.56    inference(subsumption_resolution,[],[f158,f37])).
% 1.62/0.57  fof(f158,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f157,f47])).
% 1.62/0.57  fof(f157,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f156,f48])).
% 1.62/0.57  fof(f156,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,X2,X0,k3_tmap_1(X1,sK1,sK0,X2,sK4)),k3_tmap_1(X1,sK1,sK0,X0,sK4)) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(sK0,X1) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(resolution,[],[f58,f49])).
% 1.62/0.57  fof(f58,plain,(
% 1.62/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f17])).
% 1.62/0.57  fof(f17,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.57    inference(flattening,[],[f16])).
% 1.62/0.57  fof(f16,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_pre_topc(X4,X3) | ~m1_pre_topc(X3,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).
% 1.62/0.57  fof(f496,plain,(
% 1.62/0.57    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~spl7_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f495,f50])).
% 1.62/0.57  fof(f495,plain,(
% 1.62/0.57    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(sK2,sK3) | ~spl7_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f484,f43])).
% 1.62/0.57  fof(f484,plain,(
% 1.62/0.57    v2_struct_0(sK2) | r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(sK2,sK3) | ~spl7_7),
% 1.62/0.57    inference(resolution,[],[f482,f70])).
% 1.62/0.57  fof(f70,plain,(
% 1.62/0.57    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.62/0.57    inference(forward_demodulation,[],[f52,f53])).
% 1.62/0.57  fof(f52,plain,(
% 1.62/0.57    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f482,plain,(
% 1.62/0.57    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f481,f39])).
% 1.62/0.57  fof(f481,plain,(
% 1.62/0.57    ( ! [X0] : (~l1_pre_topc(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f480,f38])).
% 1.62/0.57  fof(f480,plain,(
% 1.62/0.57    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_7),
% 1.62/0.57    inference(subsumption_resolution,[],[f479,f37])).
% 1.62/0.57  fof(f479,plain,(
% 1.62/0.57    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | r1_tmap_1(X0,sK1,k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_7),
% 1.62/0.57    inference(resolution,[],[f154,f46])).
% 1.62/0.57  fof(f154,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_7),
% 1.62/0.57    inference(avatar_component_clause,[],[f153])).
% 1.62/0.57  fof(f153,plain,(
% 1.62/0.57    spl7_7 <=> ! [X1,X0] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.62/0.57  fof(f478,plain,(
% 1.62/0.57    spl7_4),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f477])).
% 1.62/0.57  fof(f477,plain,(
% 1.62/0.57    $false | spl7_4),
% 1.62/0.57    inference(subsumption_resolution,[],[f472,f143])).
% 1.62/0.57  fof(f143,plain,(
% 1.62/0.57    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | spl7_4),
% 1.62/0.57    inference(avatar_component_clause,[],[f141])).
% 1.62/0.57  fof(f141,plain,(
% 1.62/0.57    spl7_4 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.62/0.57  fof(f472,plain,(
% 1.62/0.57    v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))),
% 1.62/0.57    inference(superposition,[],[f189,f420])).
% 1.62/0.57  fof(f476,plain,(
% 1.62/0.57    spl7_5),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f475])).
% 1.62/0.57  fof(f475,plain,(
% 1.62/0.57    $false | spl7_5),
% 1.62/0.57    inference(subsumption_resolution,[],[f471,f147])).
% 1.62/0.57  fof(f147,plain,(
% 1.62/0.57    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_5),
% 1.62/0.57    inference(avatar_component_clause,[],[f145])).
% 1.62/0.57  fof(f145,plain,(
% 1.62/0.57    spl7_5 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.62/0.57  fof(f471,plain,(
% 1.62/0.57    v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.62/0.57    inference(superposition,[],[f218,f420])).
% 1.62/0.57  fof(f474,plain,(
% 1.62/0.57    spl7_6),
% 1.62/0.57    inference(avatar_contradiction_clause,[],[f473])).
% 1.62/0.57  fof(f473,plain,(
% 1.62/0.57    $false | spl7_6),
% 1.62/0.57    inference(subsumption_resolution,[],[f470,f151])).
% 1.62/0.57  fof(f151,plain,(
% 1.62/0.57    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_6),
% 1.62/0.57    inference(avatar_component_clause,[],[f149])).
% 1.62/0.57  fof(f149,plain,(
% 1.62/0.57    spl7_6 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.62/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.62/0.57  fof(f470,plain,(
% 1.62/0.57    m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.62/0.57    inference(superposition,[],[f235,f420])).
% 1.62/0.57  fof(f155,plain,(
% 1.62/0.57    ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_7),
% 1.62/0.57    inference(avatar_split_clause,[],[f139,f153,f149,f145,f141])).
% 1.62/0.57  fof(f139,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f138,f61])).
% 1.62/0.57  fof(f138,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f137,f40])).
% 1.62/0.57  fof(f137,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f136,f41])).
% 1.62/0.57  fof(f136,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f135,f42])).
% 1.62/0.57  fof(f135,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f134,f45])).
% 1.62/0.57  fof(f134,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f133,f51])).
% 1.62/0.57  fof(f51,plain,(
% 1.62/0.57    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f133,plain,(
% 1.62/0.57    ( ! [X0,X1] : (r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,k2_tmap_1(sK0,sK1,sK4,sK3)),sK5) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.62/0.57    inference(resolution,[],[f67,f54])).
% 1.62/0.57  fof(f54,plain,(
% 1.62/0.57    r1_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK4,sK3),sK5)),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f67,plain,(
% 1.62/0.57    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,X4,X6) | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.57    inference(equality_resolution,[],[f59])).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f19])).
% 1.62/0.57  fof(f19,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.62/0.57    inference(flattening,[],[f18])).
% 1.62/0.57  fof(f18,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f8])).
% 1.62/0.57  fof(f8,axiom,(
% 1.62/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 1.62/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (30306)------------------------------
% 1.62/0.57  % (30306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (30306)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (30306)Memory used [KB]: 11129
% 1.62/0.57  % (30306)Time elapsed: 0.116 s
% 1.62/0.57  % (30306)------------------------------
% 1.62/0.57  % (30306)------------------------------
% 1.62/0.57  % (30295)Success in time 0.21 s
%------------------------------------------------------------------------------
