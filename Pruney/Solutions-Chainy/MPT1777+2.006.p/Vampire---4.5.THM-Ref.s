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
% DateTime   : Thu Dec  3 13:19:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 (1324 expanded)
%              Number of leaves         :   23 ( 675 expanded)
%              Depth                    :   47
%              Number of atoms          : 1001 (20533 expanded)
%              Number of equality atoms :   77 (2722 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f223,f338])).

fof(f338,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f336,f93])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f66,f67])).

fof(f67,plain,(
    sK5 = sK6 ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f43,f42,f41,f40,f39,f38,f37])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f66,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f336,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_8 ),
    inference(resolution,[],[f335,f280])).

fof(f280,plain,
    ( ! [X11] :
        ( r1_tarski(sK7(sK3,X11),u1_struct_0(sK2))
        | ~ m1_subset_1(X11,u1_struct_0(sK2)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f279,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f279,plain,
    ( ! [X11] :
        ( r1_tarski(sK7(sK3,X11),u1_struct_0(sK2))
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X11,u1_struct_0(sK2)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f278,f109])).

fof(f109,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f278,plain,
    ( ! [X11] :
        ( r1_tarski(sK7(sK3,X11),u1_struct_0(sK2))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X11,u1_struct_0(sK2)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f257,f99])).

fof(f99,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f73,f60])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f257,plain,
    ( ! [X11] :
        ( r1_tarski(sK7(sK3,X11),u1_struct_0(sK2))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X11,u1_struct_0(sK2)) )
    | ~ spl8_8 ),
    inference(superposition,[],[f167,f210])).

fof(f210,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl8_8
  <=> u1_struct_0(sK2) = u1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f167,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK7(X1,X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f166,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f166,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f81,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK7(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f335,plain,
    ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f334,f93])).

fof(f334,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f333,f210])).

fof(f333,plain,
    ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f332,f59])).

fof(f332,plain,
    ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f331,f109])).

fof(f331,plain,
    ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f330,f99])).

fof(f330,plain,
    ( ~ r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_8 ),
    inference(resolution,[],[f324,f82])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f323,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f322,f225])).

fof(f225,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f62,f210])).

fof(f62,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f321,f210])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f320,f226])).

fof(f226,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f63,f210])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f319,f210])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f318,f86])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f317,f210])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f316,f93])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f315,f210])).

fof(f315,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f314,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f314,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f313,f52])).

fof(f313,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f312,f53])).

fof(f312,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f311,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f311,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f310,f55])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f310,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f309,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f309,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f308,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f308,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f307,f58])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f307,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f306,f59])).

fof(f306,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f305,f60])).

% (5513)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (5531)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (5530)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (5518)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (5510)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (5525)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (5521)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (5517)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (5509)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (5527)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f305,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f304,f61])).

fof(f61,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
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
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f303,f197])).

fof(f197,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f196,f98])).

fof(f98,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f94,f53])).

fof(f94,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f73,f58])).

fof(f196,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f195,f70])).

fof(f70,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f195,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | m1_pre_topc(X1,sK3) ) ),
    inference(subsumption_resolution,[],[f194,f99])).

fof(f194,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,sK3)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(sK3) ) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,(
    ! [X1] :
      ( sK3 != sK3
      | m1_pre_topc(X1,sK3)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f188,f119])).

fof(f119,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f118,f99])).

fof(f118,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f71,f116])).

fof(f116,plain,(
    v1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f115,f57])).

fof(f115,plain,
    ( v1_pre_topc(sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f114,f98])).

fof(f114,plain,
    ( v1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f78,f64])).

fof(f64,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f188,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f182,f98])).

fof(f182,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f180,f64])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f173,f73])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X3,X1)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
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
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f302,f93])).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
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
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f301,f69])).

fof(f69,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f301,plain,(
    ! [X0] :
      ( r1_tmap_1(sK3,sK1,sK4,sK5)
      | ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
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
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f88,f92])).

fof(f92,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f68,f67])).

fof(f68,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
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
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f223,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f221,f99])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_7 ),
    inference(subsumption_resolution,[],[f220,f206])).

fof(f206,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl8_7
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f220,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f218,f70])).

fof(f218,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f217,f99])).

fof(f217,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(trivial_inequality_removal,[],[f216])).

fof(f216,plain,(
    ! [X1] :
      ( sK3 != sK3
      | m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f190,f119])).

fof(f190,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f184,f98])).

fof(f184,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3
      | m1_pre_topc(X1,sK2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f180,f64])).

fof(f211,plain,
    ( ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f202,f208,f204])).

fof(f202,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f198,f98])).

fof(f198,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f197,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f138,f73])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | u1_struct_0(X0) = u1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f74,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5512)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (5511)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (5529)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (5514)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (5532)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (5515)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (5520)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (5526)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (5523)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (5534)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (5524)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (5528)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (5519)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (5516)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (5522)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (5534)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f211,f223,f338])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~spl8_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    $false | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f336,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f66,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    sK5 = sK6),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f43,f42,f41,f40,f39,f38,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl8_8),
% 0.21/0.53    inference(resolution,[],[f335,f280])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    ( ! [X11] : (r1_tarski(sK7(sK3,X11),u1_struct_0(sK2)) | ~m1_subset_1(X11,u1_struct_0(sK2))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f279,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    ( ! [X11] : (r1_tarski(sK7(sK3,X11),u1_struct_0(sK2)) | v2_struct_0(sK3) | ~m1_subset_1(X11,u1_struct_0(sK2))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f278,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f108,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f79,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    m1_pre_topc(sK3,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ( ! [X11] : (r1_tarski(sK7(sK3,X11),u1_struct_0(sK2)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(X11,u1_struct_0(sK2))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f257,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f53])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f73,f60])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ( ! [X11] : (r1_tarski(sK7(sK3,X11),u1_struct_0(sK2)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(X11,u1_struct_0(sK2))) ) | ~spl8_8),
% 0.21/0.53    inference(superposition,[],[f167,f210])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    spl8_8 <=> u1_struct_0(sK2) = u1_struct_0(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(sK7(X1,X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.53    inference(resolution,[],[f166,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(resolution,[],[f81,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_connsp_2(sK7(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK7(X0,X1),X0,X1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f334,f93])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f333,f210])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f332,f59])).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f331,f109])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f330,f99])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    ~r1_tarski(sK7(sK3,sK5),u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl8_8),
% 0.21/0.53    inference(resolution,[],[f324,f82])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | ~spl8_8),
% 0.21/0.53    inference(resolution,[],[f323,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f50])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5)) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f322,f225])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl8_8),
% 0.21/0.53    inference(backward_demodulation,[],[f62,f210])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5)) ) | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f321,f210])).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f320,f226])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl8_8),
% 0.21/0.53    inference(backward_demodulation,[],[f63,f210])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f319,f210])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f318,f86])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f317,f210])).
% 0.21/0.53  fof(f317,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(subsumption_resolution,[],[f316,f93])).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl8_8),
% 0.21/0.53    inference(forward_demodulation,[],[f315,f210])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f314,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f313,f52])).
% 0.21/0.53  fof(f313,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f312,f53])).
% 0.21/0.53  fof(f312,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f311,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f310,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f310,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f309,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f308,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f308,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f307,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f306,f59])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f305,f60])).
% 0.21/0.53  % (5513)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (5531)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (5530)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (5518)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (5510)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5525)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (5521)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (5517)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (5509)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (5527)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f304,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    v1_funct_1(sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f303,f197])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f196,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    l1_pre_topc(sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f53])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(resolution,[],[f73,f58])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.21/0.55    inference(resolution,[],[f195,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.55  fof(f195,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK2) | m1_pre_topc(X1,sK3)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f194,f99])).
% 0.21/0.55  fof(f194,plain,(
% 0.21/0.55    ( ! [X1] : (m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(sK3)) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f193])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    ( ! [X1] : (sK3 != sK3 | m1_pre_topc(X1,sK3) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(sK3)) )),
% 0.21/0.55    inference(superposition,[],[f188,f119])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.55    inference(subsumption_resolution,[],[f118,f99])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3)),
% 0.21/0.55    inference(resolution,[],[f71,f116])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    v1_pre_topc(sK3)),
% 0.21/0.55    inference(subsumption_resolution,[],[f115,f57])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    v1_pre_topc(sK3) | v2_struct_0(sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f114,f98])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    v1_pre_topc(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.55    inference(superposition,[],[f78,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : ((v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & ~v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f182,f98])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,sK2) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK2)) )),
% 0.21/0.55    inference(superposition,[],[f180,f64])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X0,X2) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f173,f73])).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X2) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X3,X1) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f302,f93])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f301,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f88,f92])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.21/0.55    inference(backward_demodulation,[],[f68,f67])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    spl8_7),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.55  fof(f222,plain,(
% 0.21/0.55    $false | spl8_7),
% 0.21/0.55    inference(subsumption_resolution,[],[f221,f99])).
% 0.21/0.55  fof(f221,plain,(
% 0.21/0.55    ~l1_pre_topc(sK3) | spl8_7),
% 0.21/0.55    inference(subsumption_resolution,[],[f220,f206])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ~m1_pre_topc(sK3,sK2) | spl8_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f204])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    spl8_7 <=> m1_pre_topc(sK3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK3)),
% 0.21/0.55    inference(resolution,[],[f218,f70])).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f217,f99])).
% 0.21/0.55  fof(f217,plain,(
% 0.21/0.55    ( ! [X1] : (m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK3)) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f216])).
% 0.21/0.55  fof(f216,plain,(
% 0.21/0.55    ( ! [X1] : (sK3 != sK3 | m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK3)) )),
% 0.21/0.55    inference(superposition,[],[f190,f119])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f184,f98])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != sK3 | m1_pre_topc(X1,sK2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(superposition,[],[f180,f64])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ~spl8_7 | spl8_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f202,f208,f204])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    u1_struct_0(sK2) = u1_struct_0(sK3) | ~m1_pre_topc(sK3,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f198,f98])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    u1_struct_0(sK2) = u1_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2)),
% 0.21/0.55    inference(resolution,[],[f197,f140])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f73])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(resolution,[],[f112,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X1) | u1_struct_0(X0) = u1_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f74,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(flattening,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (5534)------------------------------
% 0.21/0.55  % (5534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5534)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (5534)Memory used [KB]: 10874
% 0.21/0.55  % (5534)Time elapsed: 0.119 s
% 0.21/0.55  % (5534)------------------------------
% 0.21/0.55  % (5534)------------------------------
% 0.21/0.55  % (5508)Success in time 0.187 s
%------------------------------------------------------------------------------
