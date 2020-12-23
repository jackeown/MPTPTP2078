%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:08 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  159 (1129 expanded)
%              Number of leaves         :   25 ( 574 expanded)
%              Depth                    :   27
%              Number of atoms          :  858 (17210 expanded)
%              Number of equality atoms :   61 (2259 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f323,f684,f854,f1159])).

fof(f1159,plain,
    ( spl7_1
    | ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f1158])).

fof(f1158,plain,
    ( $false
    | spl7_1
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f1157,f124])).

fof(f124,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f123,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f19,f43,f42,f41,f40,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f123,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f1157,plain,
    ( ~ v2_pre_topc(sK3)
    | spl7_1
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f1156,f111])).

fof(f111,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f109,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f61])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1156,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl7_1
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f1155,f321])).

fof(f321,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f320,f65])).

fof(f65,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f320,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f319,f110])).

fof(f110,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f319,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f151,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f151,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f1155,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | spl7_1
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f1151,f177])).

fof(f177,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_1
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1151,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl7_31 ),
    inference(resolution,[],[f495,f950])).

fof(f950,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ spl7_31 ),
    inference(superposition,[],[f214,f683])).

fof(f683,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl7_31
  <=> k2_struct_0(sK2) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f214,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f211,f124])).

fof(f211,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f111,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f495,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k2_struct_0(sK2),X0)
      | v1_tsep_1(sK2,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(superposition,[],[f101,f237])).

fof(f237,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f152,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f152,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f95,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f854,plain,(
    spl7_30 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | spl7_30 ),
    inference(subsumption_resolution,[],[f852,f679])).

fof(f679,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl7_30
  <=> r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f852,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f420,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f420,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f419,f281])).

fof(f281,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f213,f71])).

fof(f213,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f111,f72])).

fof(f419,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f418,f237])).

fof(f418,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f410,f110])).

fof(f410,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f325,f77])).

fof(f325,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(forward_demodulation,[],[f324,f65])).

fof(f324,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f315,f110])).

fof(f315,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f151,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f684,plain,
    ( ~ spl7_30
    | spl7_31 ),
    inference(avatar_split_clause,[],[f674,f681,f677])).

fof(f674,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f636,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f636,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(resolution,[],[f378,f90])).

fof(f378,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f377,f237])).

fof(f377,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f376,f281])).

fof(f376,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f368,f111])).

fof(f368,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f321,f77])).

fof(f323,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f321,f181])).

fof(f181,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl7_2
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f182,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f173,f179,f175])).

fof(f173,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f172,f66])).

fof(f66,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f172,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f171,f68])).

fof(f68,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f171,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f170,f100])).

fof(f100,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f67,f68])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f170,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f169,f68])).

fof(f169,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f168,f70])).

fof(f70,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f168,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f167,f68])).

fof(f167,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f166,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f166,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f53])).

fof(f165,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f54])).

fof(f164,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f163,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f56])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f162,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f161,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f59])).

fof(f159,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f158,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f61])).

fof(f157,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f156,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
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
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f63])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f155,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
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
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f154,f64])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f154,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ v1_tsep_1(sK2,sK3)
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
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f92,f69])).

fof(f69,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (997)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (1020)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (997)Refutation not found, incomplete strategy% (997)------------------------------
% 0.21/0.49  % (997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (997)Memory used [KB]: 10874
% 0.21/0.50  % (997)Time elapsed: 0.078 s
% 0.21/0.50  % (997)------------------------------
% 0.21/0.50  % (997)------------------------------
% 0.21/0.51  % (1001)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (1016)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (1003)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (1006)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (1002)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (1035)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (1019)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (1002)Refutation not found, incomplete strategy% (1002)------------------------------
% 0.21/0.52  % (1002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1002)Memory used [KB]: 6268
% 0.21/0.52  % (1002)Time elapsed: 0.104 s
% 0.21/0.52  % (1002)------------------------------
% 0.21/0.52  % (1002)------------------------------
% 0.21/0.52  % (1032)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (1010)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (1012)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (998)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (1014)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (1008)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (1005)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (1027)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (1034)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (1017)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (1026)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (1028)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (1007)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (1011)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (1004)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.41/0.55  % (999)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.59/0.59  % (1007)Refutation found. Thanks to Tanya!
% 1.59/0.59  % SZS status Theorem for theBenchmark
% 1.59/0.59  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f1160,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(avatar_sat_refutation,[],[f182,f323,f684,f854,f1159])).
% 1.59/0.59  fof(f1159,plain,(
% 1.59/0.59    spl7_1 | ~spl7_31),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f1158])).
% 1.59/0.59  fof(f1158,plain,(
% 1.59/0.59    $false | (spl7_1 | ~spl7_31)),
% 1.59/0.59    inference(subsumption_resolution,[],[f1157,f124])).
% 1.59/0.59  fof(f124,plain,(
% 1.59/0.59    v2_pre_topc(sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f123,f53])).
% 1.59/0.59  fof(f53,plain,(
% 1.59/0.59    v2_pre_topc(sK0)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f44,plain,(
% 1.59/0.59    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f19,f43,f42,f41,f40,f39,f38,f37])).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f40,plain,(
% 1.59/0.59    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f42,plain,(
% 1.59/0.59    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.59/0.59    inference(flattening,[],[f18])).
% 1.59/0.59  fof(f18,plain,(
% 1.59/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,negated_conjecture,(
% 1.59/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.59/0.59    inference(negated_conjecture,[],[f15])).
% 1.59/0.59  fof(f15,conjecture,(
% 1.59/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.59/0.59  fof(f123,plain,(
% 1.59/0.59    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f120,f54])).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    l1_pre_topc(sK0)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f120,plain,(
% 1.59/0.59    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.59/0.59    inference(resolution,[],[f82,f61])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    m1_pre_topc(sK3,sK0)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f82,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f32])).
% 1.59/0.59  fof(f32,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.59    inference(flattening,[],[f31])).
% 1.59/0.59  fof(f31,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.59/0.59  fof(f1157,plain,(
% 1.59/0.59    ~v2_pre_topc(sK3) | (spl7_1 | ~spl7_31)),
% 1.59/0.59    inference(subsumption_resolution,[],[f1156,f111])).
% 1.59/0.59  fof(f111,plain,(
% 1.59/0.59    l1_pre_topc(sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f109,f54])).
% 1.59/0.59  fof(f109,plain,(
% 1.59/0.59    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.59/0.59    inference(resolution,[],[f76,f61])).
% 1.59/0.59  fof(f76,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f24])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.59/0.59  fof(f1156,plain,(
% 1.59/0.59    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (spl7_1 | ~spl7_31)),
% 1.59/0.59    inference(subsumption_resolution,[],[f1155,f321])).
% 1.59/0.59  fof(f321,plain,(
% 1.59/0.59    m1_pre_topc(sK2,sK3)),
% 1.59/0.59    inference(forward_demodulation,[],[f320,f65])).
% 1.59/0.59  fof(f65,plain,(
% 1.59/0.59    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f320,plain,(
% 1.59/0.59    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f319,f110])).
% 1.59/0.59  fof(f110,plain,(
% 1.59/0.59    l1_pre_topc(sK2)),
% 1.59/0.59    inference(subsumption_resolution,[],[f108,f54])).
% 1.59/0.59  fof(f108,plain,(
% 1.59/0.59    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.59/0.59    inference(resolution,[],[f76,f59])).
% 1.59/0.59  fof(f59,plain,(
% 1.59/0.59    m1_pre_topc(sK2,sK0)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f319,plain,(
% 1.59/0.59    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2)),
% 1.59/0.59    inference(duplicate_literal_removal,[],[f313])).
% 1.59/0.59  fof(f313,plain,(
% 1.59/0.59    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 1.59/0.59    inference(resolution,[],[f151,f74])).
% 1.59/0.59  fof(f74,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f45])).
% 1.59/0.59  fof(f45,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(nnf_transformation,[],[f23])).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f7])).
% 1.59/0.59  fof(f7,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.59/0.59  fof(f151,plain,(
% 1.59/0.59    m1_pre_topc(sK2,sK2)),
% 1.59/0.59    inference(resolution,[],[f110,f73])).
% 1.59/0.59  fof(f73,plain,(
% 1.59/0.59    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f22])).
% 1.59/0.59  fof(f22,plain,(
% 1.59/0.59    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f12])).
% 1.59/0.59  fof(f12,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.59/0.59  fof(f1155,plain,(
% 1.59/0.59    ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (spl7_1 | ~spl7_31)),
% 1.59/0.59    inference(subsumption_resolution,[],[f1151,f177])).
% 1.59/0.59  fof(f177,plain,(
% 1.59/0.59    ~v1_tsep_1(sK2,sK3) | spl7_1),
% 1.59/0.59    inference(avatar_component_clause,[],[f175])).
% 1.59/0.59  fof(f175,plain,(
% 1.59/0.59    spl7_1 <=> v1_tsep_1(sK2,sK3)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.59/0.59  fof(f1151,plain,(
% 1.59/0.59    v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl7_31),
% 1.59/0.59    inference(resolution,[],[f495,f950])).
% 1.59/0.59  fof(f950,plain,(
% 1.59/0.59    v3_pre_topc(k2_struct_0(sK2),sK3) | ~spl7_31),
% 1.59/0.59    inference(superposition,[],[f214,f683])).
% 1.59/0.59  fof(f683,plain,(
% 1.59/0.59    k2_struct_0(sK2) = k2_struct_0(sK3) | ~spl7_31),
% 1.59/0.59    inference(avatar_component_clause,[],[f681])).
% 1.59/0.59  fof(f681,plain,(
% 1.59/0.59    spl7_31 <=> k2_struct_0(sK2) = k2_struct_0(sK3)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.59/0.59  fof(f214,plain,(
% 1.59/0.59    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f211,f124])).
% 1.59/0.59  fof(f211,plain,(
% 1.59/0.59    v3_pre_topc(k2_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.59/0.59    inference(resolution,[],[f111,f81])).
% 1.59/0.59  fof(f81,plain,(
% 1.59/0.59    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f30])).
% 1.59/0.59  fof(f30,plain,(
% 1.59/0.59    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.59    inference(flattening,[],[f29])).
% 1.59/0.59  fof(f29,plain,(
% 1.59/0.59    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f8])).
% 1.59/0.59  fof(f8,axiom,(
% 1.59/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.59/0.59  fof(f495,plain,(
% 1.59/0.59    ( ! [X0] : (~v3_pre_topc(k2_struct_0(sK2),X0) | v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(superposition,[],[f101,f237])).
% 1.59/0.59  fof(f237,plain,(
% 1.59/0.59    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.59/0.59    inference(resolution,[],[f152,f71])).
% 1.59/0.59  fof(f71,plain,(
% 1.59/0.59    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  fof(f20,plain,(
% 1.59/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.59/0.59  fof(f152,plain,(
% 1.59/0.59    l1_struct_0(sK2)),
% 1.59/0.59    inference(resolution,[],[f110,f72])).
% 1.59/0.59  fof(f72,plain,(
% 1.59/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,plain,(
% 1.59/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.59/0.59  fof(f101,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(subsumption_resolution,[],[f95,f77])).
% 1.59/0.59  fof(f77,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f25])).
% 1.59/0.59  fof(f25,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.59/0.59  fof(f95,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(equality_resolution,[],[f85])).
% 1.59/0.59  fof(f85,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f48])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.59    inference(flattening,[],[f47])).
% 1.59/0.59  fof(f47,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.59    inference(nnf_transformation,[],[f36])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.59/0.59    inference(flattening,[],[f35])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f10])).
% 1.59/0.59  fof(f10,axiom,(
% 1.59/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.59/0.59  fof(f854,plain,(
% 1.59/0.59    spl7_30),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f853])).
% 1.59/0.59  fof(f853,plain,(
% 1.59/0.59    $false | spl7_30),
% 1.59/0.59    inference(subsumption_resolution,[],[f852,f679])).
% 1.59/0.59  fof(f679,plain,(
% 1.59/0.59    ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) | spl7_30),
% 1.59/0.59    inference(avatar_component_clause,[],[f677])).
% 1.59/0.59  fof(f677,plain,(
% 1.59/0.59    spl7_30 <=> r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.59/0.59  fof(f852,plain,(
% 1.59/0.59    r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.59/0.59    inference(resolution,[],[f420,f90])).
% 1.59/0.59  fof(f90,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f51])).
% 1.59/0.59  fof(f51,plain,(
% 1.59/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.59/0.59    inference(nnf_transformation,[],[f2])).
% 1.59/0.59  fof(f2,axiom,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.59/0.59  fof(f420,plain,(
% 1.59/0.59    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.59/0.59    inference(forward_demodulation,[],[f419,f281])).
% 1.59/0.59  fof(f281,plain,(
% 1.59/0.59    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.59/0.59    inference(resolution,[],[f213,f71])).
% 1.59/0.59  fof(f213,plain,(
% 1.59/0.59    l1_struct_0(sK3)),
% 1.59/0.59    inference(resolution,[],[f111,f72])).
% 1.59/0.59  fof(f419,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK2)))),
% 1.59/0.59    inference(forward_demodulation,[],[f418,f237])).
% 1.59/0.59  fof(f418,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f410,f110])).
% 1.59/0.59  fof(f410,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.59/0.59    inference(resolution,[],[f325,f77])).
% 1.59/0.59  fof(f325,plain,(
% 1.59/0.59    m1_pre_topc(sK3,sK2)),
% 1.59/0.59    inference(forward_demodulation,[],[f324,f65])).
% 1.59/0.59  fof(f324,plain,(
% 1.59/0.59    m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)),
% 1.59/0.59    inference(subsumption_resolution,[],[f315,f110])).
% 1.59/0.59  fof(f315,plain,(
% 1.59/0.59    m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) | ~l1_pre_topc(sK2)),
% 1.59/0.59    inference(resolution,[],[f151,f78])).
% 1.59/0.59  fof(f78,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f26])).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f17])).
% 1.59/0.59  fof(f17,plain,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 1.59/0.59    inference(pure_predicate_removal,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.59/0.59  fof(f684,plain,(
% 1.59/0.59    ~spl7_30 | spl7_31),
% 1.59/0.59    inference(avatar_split_clause,[],[f674,f681,f677])).
% 1.59/0.59  fof(f674,plain,(
% 1.59/0.59    k2_struct_0(sK2) = k2_struct_0(sK3) | ~r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))),
% 1.59/0.59    inference(resolution,[],[f636,f89])).
% 1.59/0.59  fof(f89,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f50])).
% 1.59/0.59  fof(f50,plain,(
% 1.59/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.59    inference(flattening,[],[f49])).
% 1.59/0.59  fof(f49,plain,(
% 1.59/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.59    inference(nnf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.59  fof(f636,plain,(
% 1.59/0.59    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))),
% 1.59/0.59    inference(resolution,[],[f378,f90])).
% 1.59/0.59  fof(f378,plain,(
% 1.59/0.59    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))),
% 1.59/0.59    inference(forward_demodulation,[],[f377,f237])).
% 1.59/0.59  fof(f377,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK3)))),
% 1.59/0.59    inference(forward_demodulation,[],[f376,f281])).
% 1.59/0.59  fof(f376,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.59/0.59    inference(subsumption_resolution,[],[f368,f111])).
% 1.59/0.59  fof(f368,plain,(
% 1.59/0.59    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 1.59/0.59    inference(resolution,[],[f321,f77])).
% 1.59/0.59  fof(f323,plain,(
% 1.59/0.59    spl7_2),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f322])).
% 1.59/0.59  fof(f322,plain,(
% 1.59/0.59    $false | spl7_2),
% 1.59/0.59    inference(subsumption_resolution,[],[f321,f181])).
% 1.59/0.59  fof(f181,plain,(
% 1.59/0.59    ~m1_pre_topc(sK2,sK3) | spl7_2),
% 1.59/0.59    inference(avatar_component_clause,[],[f179])).
% 1.59/0.59  fof(f179,plain,(
% 1.59/0.59    spl7_2 <=> m1_pre_topc(sK2,sK3)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.59/0.59  fof(f182,plain,(
% 1.59/0.59    ~spl7_1 | ~spl7_2),
% 1.59/0.59    inference(avatar_split_clause,[],[f173,f179,f175])).
% 1.59/0.59  fof(f173,plain,(
% 1.59/0.59    ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f172,f66])).
% 1.59/0.59  fof(f66,plain,(
% 1.59/0.59    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f172,plain,(
% 1.59/0.59    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(forward_demodulation,[],[f171,f68])).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    sK5 = sK6),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f171,plain,(
% 1.59/0.59    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f170,f100])).
% 1.59/0.59  fof(f100,plain,(
% 1.59/0.59    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.59/0.59    inference(forward_demodulation,[],[f67,f68])).
% 1.59/0.59  fof(f67,plain,(
% 1.59/0.59    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f170,plain,(
% 1.59/0.59    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(forward_demodulation,[],[f169,f68])).
% 1.59/0.59  fof(f169,plain,(
% 1.59/0.59    ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f168,f70])).
% 1.59/0.59  fof(f70,plain,(
% 1.59/0.59    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f168,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(forward_demodulation,[],[f167,f68])).
% 1.59/0.59  fof(f167,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3)),
% 1.59/0.59    inference(subsumption_resolution,[],[f166,f52])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ~v2_struct_0(sK0)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f166,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f165,f53])).
% 1.59/0.59  fof(f165,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f164,f54])).
% 1.59/0.59  fof(f164,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f163,f55])).
% 1.59/0.59  fof(f55,plain,(
% 1.59/0.59    ~v2_struct_0(sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f163,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f162,f56])).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    v2_pre_topc(sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f162,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f161,f57])).
% 1.59/0.59  fof(f57,plain,(
% 1.59/0.59    l1_pre_topc(sK1)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f161,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f160,f58])).
% 1.59/0.59  fof(f58,plain,(
% 1.59/0.59    ~v2_struct_0(sK2)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f160,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f159,f59])).
% 1.59/0.59  fof(f159,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f158,f60])).
% 1.59/0.59  fof(f60,plain,(
% 1.59/0.59    ~v2_struct_0(sK3)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f158,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f157,f61])).
% 1.59/0.59  fof(f157,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f156,f62])).
% 1.59/0.59  fof(f62,plain,(
% 1.59/0.59    v1_funct_1(sK4)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f156,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f155,f63])).
% 1.59/0.59  fof(f63,plain,(
% 1.59/0.59    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f155,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(subsumption_resolution,[],[f154,f64])).
% 1.59/0.59  fof(f64,plain,(
% 1.59/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f154,plain,(
% 1.59/0.59    r1_tmap_1(sK3,sK1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.59/0.59    inference(resolution,[],[f92,f69])).
% 1.59/0.59  fof(f69,plain,(
% 1.59/0.59    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.59/0.59    inference(cnf_transformation,[],[f44])).
% 1.59/0.59  fof(f92,plain,(
% 1.59/0.59    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | r1_tmap_1(X3,X1,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.59    inference(equality_resolution,[],[f80])).
% 1.59/0.59  fof(f80,plain,(
% 1.59/0.59    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f46])).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.59    inference(nnf_transformation,[],[f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.59    inference(flattening,[],[f27])).
% 1.59/0.59  fof(f27,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f14])).
% 1.59/0.59  fof(f14,axiom,(
% 1.59/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (1007)------------------------------
% 1.59/0.59  % (1007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (1007)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (1007)Memory used [KB]: 11129
% 1.59/0.59  % (1007)Time elapsed: 0.188 s
% 1.59/0.59  % (1007)------------------------------
% 1.59/0.59  % (1007)------------------------------
% 1.59/0.60  % (996)Success in time 0.234 s
%------------------------------------------------------------------------------
