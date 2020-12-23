%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 991 expanded)
%              Number of leaves         :   23 ( 480 expanded)
%              Depth                    :   24
%              Number of atoms          :  967 (16620 expanded)
%              Number of equality atoms :   27 ( 679 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f632,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f507,f529,f567,f631])).

fof(f631,plain,(
    ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f629,f64])).

fof(f64,plain,(
    m1_subset_1(sK8,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tmap_1(sK3,sK5,sK7,sK8)
    & r1_tmap_1(sK3,sK4,sK6,sK8)
    & m1_subset_1(sK8,u1_struct_0(sK3))
    & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),sK6,sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
    & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK4))
    & u1_struct_0(sK4) = u1_struct_0(sK5)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f11,f31,f30,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_tmap_1(X0,X2,X4,X5)
                            & r1_tmap_1(X0,X1,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                & u1_struct_0(X1) = u1_struct_0(X2)
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
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
                          ( ~ r1_tmap_1(sK3,X2,X4,X5)
                          & r1_tmap_1(sK3,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(sK3)) )
                      & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_tmap_1(sK3,X2,X4,X5)
                        & r1_tmap_1(sK3,X1,X3,X5)
                        & m1_subset_1(X5,u1_struct_0(sK3)) )
                    & r1_funct_2(u1_struct_0(sK3),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X2),X3,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                    & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X2))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
            & u1_struct_0(X1) = u1_struct_0(X2)
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_tmap_1(sK3,X2,X4,X5)
                      & r1_tmap_1(sK3,sK4,X3,X5)
                      & m1_subset_1(X5,u1_struct_0(sK3)) )
                  & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(X2),X3,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                  & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X2))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
              & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK4))
              & v1_funct_1(X3) )
          & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK4))
          & u1_struct_0(X2) = u1_struct_0(sK4)
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_tmap_1(sK3,X2,X4,X5)
                    & r1_tmap_1(sK3,sK4,X3,X5)
                    & m1_subset_1(X5,u1_struct_0(sK3)) )
                & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(X2),X3,X4)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X2))))
                & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X2))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
            & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK4))
            & v1_funct_1(X3) )
        & r1_tarski(u1_pre_topc(X2),u1_pre_topc(sK4))
        & u1_struct_0(X2) = u1_struct_0(sK4)
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_tmap_1(sK3,sK5,X4,X5)
                  & r1_tmap_1(sK3,sK4,X3,X5)
                  & m1_subset_1(X5,u1_struct_0(sK3)) )
              & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),X3,X4)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
              & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK5))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
          & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK4))
          & v1_funct_1(X3) )
      & r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK4))
      & u1_struct_0(sK4) = u1_struct_0(sK5)
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_tmap_1(sK3,sK5,X4,X5)
                & r1_tmap_1(sK3,sK4,X3,X5)
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),X3,X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK5))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
        & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(sK4))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_tmap_1(sK3,sK5,X4,X5)
              & r1_tmap_1(sK3,sK4,sK6,X5)
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),sK6,X4)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK5))
          & v1_funct_1(X4) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
      & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r1_tmap_1(sK3,sK5,X4,X5)
            & r1_tmap_1(sK3,sK4,sK6,X5)
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),sK6,X4)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK5))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r1_tmap_1(sK3,sK5,sK7,X5)
          & r1_tmap_1(sK3,sK4,sK6,X5)
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),sK6,sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5))))
      & v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X5] :
        ( ~ r1_tmap_1(sK3,sK5,sK7,X5)
        & r1_tmap_1(sK3,sK4,sK6,X5)
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ~ r1_tmap_1(sK3,sK5,sK7,sK8)
      & r1_tmap_1(sK3,sK4,sK6,sK8)
      & m1_subset_1(sK8,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
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
                          ( ~ r1_tmap_1(X0,X2,X4,X5)
                          & r1_tmap_1(X0,X1,X3,X5)
                          & m1_subset_1(X5,u1_struct_0(X0)) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
              & u1_struct_0(X1) = u1_struct_0(X2)
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                    & u1_struct_0(X1) = u1_struct_0(X2) )
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                            & v1_funct_1(X4) )
                         => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                           => ! [X5] :
                                ( m1_subset_1(X5,u1_struct_0(X0))
                               => ( r1_tmap_1(X0,X1,X3,X5)
                                 => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1))
                  & u1_struct_0(X1) = u1_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),X3,X4)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( r1_tmap_1(X0,X1,X3,X5)
                               => r1_tmap_1(X0,X2,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tmap_1)).

fof(f629,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ spl11_14 ),
    inference(resolution,[],[f624,f66])).

fof(f66,plain,(
    ~ r1_tmap_1(sK3,sK5,sK7,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f624,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK7,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f622,f528])).

fof(f528,plain,
    ( ! [X4,X5,X3] : sP1(X3,X4,sK5,X5)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl11_14
  <=> ! [X3,X5,X4] : sP1(X3,X4,sK5,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f622,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ sP1(X0,sK3,sK5,sK7)
      | r1_tmap_1(sK3,sK5,sK7,X0) ) ),
    inference(resolution,[],[f611,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ sP1(X3,X2,X1,X0)
      | r1_tmap_1(X2,X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_tmap_1(X2,X1,X0,X3)
          | ~ sP1(X3,X2,X1,X0) )
        & ( sP1(X3,X2,X1,X0)
          | ~ r1_tmap_1(X2,X1,X0,X3) ) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ( r1_tmap_1(X0,X1,X2,X3)
          | ~ sP1(X3,X0,X1,X2) )
        & ( sP1(X3,X0,X1,X2)
          | ~ r1_tmap_1(X0,X1,X2,X3) ) )
      | ~ sP2(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( ( r1_tmap_1(X0,X1,X2,X3)
      <=> sP1(X3,X0,X1,X2) )
      | ~ sP2(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f611,plain,(
    ! [X0] :
      ( sP2(sK7,sK5,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f610,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f610,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK7,sK5,sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f609,f47])).

fof(f47,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f609,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK7,sK5,sK3,X0)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f608,f48])).

fof(f48,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f608,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK7,sK5,sK3,X0)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f607,f60])).

fof(f60,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f607,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK7,sK5,sK3,X0)
      | ~ v1_funct_1(sK7)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f602,f91])).

fof(f91,plain,(
    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f61,f55])).

fof(f55,plain,(
    u1_struct_0(sK4) = u1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f602,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(sK7,sK5,sK3,X0)
      | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(sK7)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f92,f352])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP2(X0,sK5,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f351,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f351,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP2(X0,sK5,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
      | ~ v1_funct_1(X0)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f350,f53])).

fof(f53,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f350,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP2(X0,sK5,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f330,f54])).

fof(f54,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP2(X0,sK5,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK4))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f81,f55])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP2(X2,X1,X0,X3)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP2(X2,X1,X0,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f24,f23,f22])).

fof(f22,plain,(
    ! [X4,X2,X1,X0,X3] :
      ( sP0(X4,X2,X1,X0,X3)
    <=> ? [X5] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
          & r2_hidden(X3,X5)
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X3,X0,X1,X2] :
      ( sP1(X3,X0,X1,X2)
    <=> ! [X4] :
          ( sP0(X4,X2,X1,X0,X3)
          | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
          | ~ v3_pre_topc(X4,X1)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & r2_hidden(X3,X5)
                            & v3_pre_topc(X5,X0)
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                        | ~ v3_pre_topc(X4,X1)
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( ! [X5] :
                                ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
                               => ~ ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                                    & r2_hidden(X3,X5)
                                    & v3_pre_topc(X5,X0) ) )
                            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
                            & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tmap_1)).

fof(f92,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(forward_demodulation,[],[f62,f55])).

fof(f62,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f567,plain,
    ( spl11_14
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f566,f120,f527])).

fof(f120,plain,
    ( spl11_5
  <=> ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f566,plain,
    ( ! [X2,X3,X1] : sP1(X1,X2,sK5,X3)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f564,f54])).

fof(f564,plain,
    ( ! [X2,X3,X1] :
        ( sP1(X1,X2,sK5,X3)
        | ~ l1_pre_topc(sK5) )
    | ~ spl11_5 ),
    inference(resolution,[],[f121,f156])).

fof(f156,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK9(X4,X5,X6,X7),u1_pre_topc(X6))
      | sP1(X4,X5,X6,X7)
      | ~ l1_pre_topc(X6) ) ),
    inference(subsumption_resolution,[],[f149,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X3),X2)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ~ sP0(sK9(X0,X1,X2,X3),X3,X2,X1,X0)
          & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK9(X0,X1,X2,X3))
          & v3_pre_topc(sK9(X0,X1,X2,X3),X2)
          & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X5] :
            ( sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
            | ~ v3_pre_topc(X5,X2)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ sP0(X4,X3,X2,X1,X0)
          & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X4)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ sP0(sK9(X0,X1,X2,X3),X3,X2,X1,X0)
        & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK9(X0,X1,X2,X3))
        & v3_pre_topc(sK9(X0,X1,X2,X3),X2)
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ sP0(X4,X3,X2,X1,X0)
            & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X4)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X5] :
            ( sP0(X5,X3,X2,X1,X0)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
            | ~ v3_pre_topc(X5,X2)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X3,X0,X1,X2] :
      ( ( sP1(X3,X0,X1,X2)
        | ? [X4] :
            ( ~ sP0(X4,X2,X1,X0,X3)
            & r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
            & v3_pre_topc(X4,X1)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( sP0(X4,X2,X1,X0,X3)
            | ~ r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X4)
            | ~ v3_pre_topc(X4,X1)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP1(X3,X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( sP1(X4,X5,X6,X7)
      | ~ v3_pre_topc(sK9(X4,X5,X6,X7),X6)
      | r2_hidden(sK9(X4,X5,X6,X7),u1_pre_topc(X6))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK5))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f529,plain,
    ( spl11_14
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f261,f168,f527])).

fof(f168,plain,
    ( spl11_8
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f261,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(u1_struct_0(sK4))
      | sP1(X3,X4,sK5,X5) ) ),
    inference(forward_demodulation,[],[f259,f55])).

fof(f259,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4,sK5,X5)
      | ~ v1_xboole_0(u1_struct_0(sK5)) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4,sK5,X5)
      | ~ v1_xboole_0(u1_struct_0(sK5))
      | sP1(X3,X4,sK5,X5) ) ),
    inference(resolution,[],[f217,f153])).

fof(f153,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( ~ r2_hidden(X23,sK9(X19,X20,X21,X22))
      | ~ v1_xboole_0(u1_struct_0(X21))
      | sP1(X19,X20,X21,X22) ) ),
    inference(resolution,[],[f72,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK4),X1,X2),sK9(X2,X0,sK5,X1))
      | sP1(X2,X0,sK5,X1) ) ),
    inference(superposition,[],[f74,f55])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),sK9(X0,X1,X2,X3))
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f507,plain,
    ( spl11_4
    | spl11_8 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl11_4
    | spl11_8 ),
    inference(subsumption_resolution,[],[f505,f65])).

fof(f65,plain,(
    r1_tmap_1(sK3,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f32])).

fof(f505,plain,
    ( ~ r1_tmap_1(sK3,sK4,sK6,sK8)
    | spl11_4
    | spl11_8 ),
    inference(subsumption_resolution,[],[f504,f64])).

fof(f504,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK3,sK4,sK6,sK8)
    | spl11_4
    | spl11_8 ),
    inference(resolution,[],[f503,f375])).

fof(f375,plain,
    ( ~ r1_tmap_1(sK3,sK5,sK6,sK8)
    | spl11_8 ),
    inference(backward_demodulation,[],[f66,f373])).

fof(f373,plain,
    ( sK6 = sK7
    | spl11_8 ),
    inference(subsumption_resolution,[],[f372,f170])).

fof(f170,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl11_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f372,plain,
    ( sK6 = sK7
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f371,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f371,plain,
    ( sK6 = sK7
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f370,f58])).

fof(f58,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f370,plain,
    ( sK6 = sK7
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f369,f59])).

fof(f59,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f369,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f368,f60])).

fof(f368,plain,
    ( sK6 = sK7
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f367,f91])).

fof(f367,plain,
    ( sK6 = sK7
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f366,f92])).

fof(f366,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( sK6 = sK7
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK7,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f87,f93])).

fof(f93,plain,(
    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK4),sK6,sK7) ),
    inference(forward_demodulation,[],[f63,f55])).

fof(f63,plain,(
    r1_funct_2(u1_struct_0(sK3),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK5),sK6,sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f503,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK4,sK6,X0) )
    | spl11_4 ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK4,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl11_4 ),
    inference(resolution,[],[f496,f354])).

fof(f354,plain,(
    ! [X1] :
      ( sP1(X1,sK3,sK4,sK6)
      | ~ r1_tmap_1(sK3,sK4,sK6,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f338,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tmap_1(X2,X1,X0,X3)
      | sP1(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f338,plain,(
    ! [X4] :
      ( sP2(sK6,sK4,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f337,f46])).

fof(f337,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f336,f47])).

fof(f336,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f335,f48])).

fof(f335,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f334,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f334,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f333,f50])).

fof(f50,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f333,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f332,f51])).

fof(f51,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f332,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f331,f57])).

fof(f331,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f327,f58])).

fof(f327,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK3))
      | sP2(sK6,sK4,sK3,X4)
      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f81,f59])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ sP1(X0,sK3,sK4,sK6)
        | r1_tmap_1(sK3,sK5,sK6,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | spl11_4 ),
    inference(resolution,[],[f494,f428])).

fof(f428,plain,
    ( ! [X6,X4,X5] :
        ( sP1(X4,X5,sK5,X6)
        | ~ sP1(X4,X5,sK4,X6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f310,f426])).

fof(f426,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(sK9(X3,X4,sK5,X5),X5,sK4,X4,X3)
      | sP1(X3,X4,sK5,X5) ) ),
    inference(resolution,[],[f424,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(sK9(X0,X1,X2,X3),X3,X2,X1,X0)
      | sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f424,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,sK5,X2,X3)
      | ~ sP0(X0,X1,sK4,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,sK5,X2,X3)
      | ~ sP0(X0,X1,sK4,X2,X3)
      | ~ sP0(X0,X1,sK4,X2,X3) ) ),
    inference(resolution,[],[f415,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X4,sK10(X0,X1,X2,X3,X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
            | ~ r2_hidden(X4,X5)
            | ~ v3_pre_topc(X5,X3)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) )
      & ( ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK10(X0,X1,X2,X3,X4)),X0)
          & r2_hidden(X4,sK10(X0,X1,X2,X3,X4))
          & v3_pre_topc(sK10(X0,X1,X2,X3,X4),X3)
          & m1_subset_1(sK10(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3))) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f41,f42])).

fof(f42,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X6),X0)
          & r2_hidden(X4,X6)
          & v3_pre_topc(X6,X3)
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3))) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK10(X0,X1,X2,X3,X4)),X0)
        & r2_hidden(X4,sK10(X0,X1,X2,X3,X4))
        & v3_pre_topc(sK10(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK10(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
            | ~ r2_hidden(X4,X5)
            | ~ v3_pre_topc(X5,X3)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) )
      & ( ? [X6] :
            ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X6),X0)
            & r2_hidden(X4,X6)
            & v3_pre_topc(X6,X3)
            & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3))) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X1,X0,X3] :
      ( ( sP0(X4,X2,X1,X0,X3)
        | ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
            | ~ r2_hidden(X3,X5)
            | ~ v3_pre_topc(X5,X0)
            | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X5] :
            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
            & r2_hidden(X3,X5)
            & v3_pre_topc(X5,X0)
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X4,X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f415,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,sK10(X0,X1,sK4,X2,X4))
      | sP0(X0,X1,sK5,X2,X3)
      | ~ sP0(X0,X1,sK4,X2,X4) ) ),
    inference(subsumption_resolution,[],[f414,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f414,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,sK5,X2,X3)
      | ~ r2_hidden(X3,sK10(X0,X1,sK4,X2,X4))
      | ~ m1_subset_1(sK10(X0,X1,sK4,X2,X4),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,sK4,X2,X4) ) ),
    inference(subsumption_resolution,[],[f409,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v3_pre_topc(sK10(X0,X1,X2,X3,X4),X3)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f409,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,sK5,X2,X3)
      | ~ r2_hidden(X3,sK10(X0,X1,sK4,X2,X4))
      | ~ v3_pre_topc(sK10(X0,X1,sK4,X2,X4),X2)
      | ~ m1_subset_1(sK10(X0,X1,sK4,X2,X4),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,sK4,X2,X4) ) ),
    inference(resolution,[],[f267,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,sK10(X0,X1,X2,X3,X4)),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f267,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X1,X2),X3)
      | sP0(X3,X1,sK5,X0,X4)
      | ~ r2_hidden(X4,X2)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f80,f55])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1,X5),X0)
      | sP0(X0,X1,X2,X3,X4)
      | ~ r2_hidden(X4,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f310,plain,
    ( ! [X6,X4,X5] :
        ( sP0(sK9(X4,X5,sK5,X6),X6,sK4,X5,X4)
        | ~ sP1(X4,X5,sK4,X6)
        | sP1(X4,X5,sK5,X6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f309,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,sK5,X2),k1_zfmisc_1(u1_struct_0(sK4)))
      | sP1(X0,X1,sK5,X2) ) ),
    inference(superposition,[],[f72,f55])).

fof(f309,plain,
    ( ! [X6,X4,X5] :
        ( sP0(sK9(X4,X5,sK5,X6),X6,sK4,X5,X4)
        | ~ m1_subset_1(sK9(X4,X5,sK5,X6),k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ sP1(X4,X5,sK4,X6)
        | sP1(X4,X5,sK5,X6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f302,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( v3_pre_topc(sK9(X0,X1,sK5,X2),sK4)
        | sP1(X0,X1,sK5,X2) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f191,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,sK5,X2),u1_pre_topc(sK4))
      | sP1(X0,X1,sK5,X2) ) ),
    inference(resolution,[],[f164,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK5))
      | m1_subset_1(X0,u1_pre_topc(sK4)) ) ),
    inference(resolution,[],[f123,f56])).

fof(f56,plain,(
    r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f85,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f164,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK9(X3,X4,sK5,X5),u1_pre_topc(sK5))
      | sP1(X3,X4,sK5,X5) ) ),
    inference(subsumption_resolution,[],[f158,f73])).

fof(f158,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4,sK5,X5)
      | ~ v3_pre_topc(sK9(X3,X4,sK5,X5),sK5)
      | r2_hidden(sK9(X3,X4,sK5,X5),u1_pre_topc(sK5)) ) ),
    inference(resolution,[],[f155,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v3_pre_topc(X0,sK5)
      | r2_hidden(X0,u1_pre_topc(sK5)) ) ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v3_pre_topc(X0,sK5)
      | r2_hidden(X0,u1_pre_topc(sK5))
      | ~ l1_pre_topc(sK5) ) ),
    inference(superposition,[],[f67,f55])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,X1,sK5,X2)
        | v3_pre_topc(sK9(X0,X1,sK5,X2),sK4)
        | ~ m1_subset_1(sK9(X0,X1,sK5,X2),u1_pre_topc(sK4)) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f190,f118])).

fof(f118,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK4))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl11_4
  <=> v1_xboole_0(u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,sK5,X2)
      | v3_pre_topc(sK9(X0,X1,sK5,X2),sK4)
      | v1_xboole_0(u1_pre_topc(sK4))
      | ~ m1_subset_1(sK9(X0,X1,sK5,X2),u1_pre_topc(sK4)) ) ),
    inference(resolution,[],[f165,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f165,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK9(X6,X7,sK5,X8),u1_pre_topc(sK4))
      | sP1(X6,X7,sK5,X8)
      | v3_pre_topc(sK9(X6,X7,sK5,X8),sK4) ) ),
    inference(subsumption_resolution,[],[f159,f51])).

fof(f159,plain,(
    ! [X6,X8,X7] :
      ( sP1(X6,X7,sK5,X8)
      | ~ r2_hidden(sK9(X6,X7,sK5,X8),u1_pre_topc(sK4))
      | v3_pre_topc(sK9(X6,X7,sK5,X8),sK4)
      | ~ l1_pre_topc(sK4) ) ),
    inference(resolution,[],[f155,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f302,plain,(
    ! [X6,X4,X5] :
      ( sP0(sK9(X4,X5,sK5,X6),X6,sK4,X5,X4)
      | ~ v3_pre_topc(sK9(X4,X5,sK5,X6),sK4)
      | ~ m1_subset_1(sK9(X4,X5,sK5,X6),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ sP1(X4,X5,sK4,X6)
      | sP1(X4,X5,sK5,X6) ) ),
    inference(resolution,[],[f71,f217])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X5)
      | sP0(X5,X3,X2,X1,X0)
      | ~ v3_pre_topc(X5,X2)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f494,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK3,sK5,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r1_tmap_1(sK3,sK5,sK6,X0) ) ),
    inference(resolution,[],[f490,f70])).

fof(f490,plain,(
    ! [X3] :
      ( sP2(sK6,sK5,sK3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f489,f46])).

fof(f489,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f488,f47])).

fof(f488,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f487,f48])).

fof(f487,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f486,f57])).

fof(f486,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X3)
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f484,f58])).

fof(f484,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK3))
      | sP2(sK6,sK5,sK3,X3)
      | ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK4))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f352,f59])).

fof(f122,plain,
    ( ~ spl11_4
    | spl11_5 ),
    inference(avatar_split_clause,[],[f112,f120,f116])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK5))
      | ~ v1_xboole_0(u1_pre_topc(sK4)) ) ),
    inference(resolution,[],[f97,f56])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f86,f84])).

%------------------------------------------------------------------------------
