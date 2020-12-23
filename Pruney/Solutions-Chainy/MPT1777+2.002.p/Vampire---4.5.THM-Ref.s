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

% Result     : Theorem 1.89s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  218 (3009 expanded)
%              Number of leaves         :   30 (1556 expanded)
%              Depth                    :   43
%              Number of atoms          : 1216 (47298 expanded)
%              Number of equality atoms :  119 (6417 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1761,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f201,f343,f790,f1108,f1749])).

fof(f1749,plain,
    ( ~ spl7_2
    | ~ spl7_25 ),
    inference(avatar_contradiction_clause,[],[f1748])).

fof(f1748,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f1747,f173])).

fof(f173,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f28,f66,f65,f64,f63,f62,f61,f60])).

fof(f60,plain,
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

fof(f61,plain,
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

fof(f62,plain,
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

fof(f63,plain,
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

fof(f64,plain,
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

fof(f65,plain,
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

fof(f66,plain,
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

fof(f1747,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_2
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f1742,f94])).

fof(f94,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f1742,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_2
    | ~ spl7_25 ),
    inference(resolution,[],[f789,f1061])).

fof(f1061,plain,
    ( r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f231,f1058])).

fof(f1058,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f1052,f680])).

fof(f680,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f675,f151])).

fof(f151,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f144,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f144,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f83,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f83,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f675,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f483,f99])).

fof(f99,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f483,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f482,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f481,f148])).

fof(f148,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f147,f77])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f147,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f141,f78])).

fof(f141,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f83,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f481,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f480,f151])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f479,f79])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f478,f80])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f478,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f477,f81])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f476,f86])).

fof(f86,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f474,f415])).

fof(f415,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f87,f414])).

fof(f414,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl7_2 ),
    inference(trivial_inequality_removal,[],[f413])).

fof(f413,plain,
    ( sK3 != sK3
    | u1_struct_0(sK2) = u1_struct_0(sK3)
    | ~ spl7_2 ),
    inference(superposition,[],[f200,f230])).

fof(f230,plain,(
    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f229,f166])).

fof(f166,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f159,f78])).

fof(f159,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f104])).

fof(f85,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f229,plain,
    ( sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f228,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f228,plain,(
    v1_pre_topc(sK3) ),
    inference(forward_demodulation,[],[f149,f89])).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f67])).

fof(f149,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f142,f78])).

fof(f142,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f83,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f200,plain,
    ( ! [X6,X7] :
        ( sK3 != g1_pre_topc(X6,X7)
        | u1_struct_0(sK2) = X6 )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl7_2
  <=> ! [X7,X6] :
        ( sK3 != g1_pre_topc(X6,X7)
        | u1_struct_0(sK2) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f87,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f416,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f416,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f88,f414])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f1052,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f851,f382])).

fof(f382,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f381,f151])).

fof(f381,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f191,f99])).

fof(f191,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK2)
      | m1_pre_topc(X2,sK3)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f184,f151])).

fof(f184,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X2,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f102,f89])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f851,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f850,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f850,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f849,f77])).

fof(f849,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f844,f78])).

fof(f844,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f791,f85])).

fof(f791,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f227,f414])).

fof(f227,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f226,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f226,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f225,f79])).

fof(f225,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f224,f80])).

fof(f224,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f223,f81])).

fof(f223,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f222,f86])).

fof(f222,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f213,f87])).

fof(f213,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f88,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f231,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(forward_demodulation,[],[f93,f92])).

fof(f93,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f67])).

fof(f789,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f788])).

fof(f788,plain,
    ( spl7_25
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1108,plain,
    ( ~ spl7_2
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f1107])).

fof(f1107,plain,
    ( $false
    | ~ spl7_2
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1106,f382])).

fof(f1106,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_2
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1105,f767])).

fof(f767,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl7_23
  <=> v1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1105,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f1103,f420])).

fof(f420,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f211,f414])).

fof(f211,plain,(
    v3_pre_topc(u1_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f210,f163])).

fof(f163,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f162,f77])).

fof(f162,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f156,f78])).

fof(f156,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f85,f117])).

fof(f210,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f209,f166])).

fof(f209,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(superposition,[],[f116,f170])).

fof(f170,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f168,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f168,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f166,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f116,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f1103,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f467,f424])).

fof(f424,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f312,f414])).

fof(f312,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f306,f151])).

fof(f306,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f300,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f300,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f298,f166])).

fof(f298,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f190,f99])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f182,f151])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f110,f89])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f467,plain,
    ( ! [X26] :
        ( ~ m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(u1_struct_0(X26),sK3)
        | v1_tsep_1(X26,sK3)
        | ~ m1_pre_topc(X26,sK3) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f466,f163])).

fof(f466,plain,
    ( ! [X26] :
        ( ~ m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(u1_struct_0(X26),sK3)
        | v1_tsep_1(X26,sK3)
        | ~ m1_pre_topc(X26,sK3)
        | ~ v2_pre_topc(sK3) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f442,f166])).

fof(f442,plain,
    ( ! [X26] :
        ( ~ m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v3_pre_topc(u1_struct_0(X26),sK3)
        | v1_tsep_1(X26,sK3)
        | ~ m1_pre_topc(X26,sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3) )
    | ~ spl7_2 ),
    inference(superposition,[],[f132,f414])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f790,plain,
    ( ~ spl7_23
    | spl7_25
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f786,f199,f788,f765])).

fof(f786,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ v1_tsep_1(sK2,sK3) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f785,f415])).

fof(f785,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ v1_tsep_1(sK2,sK3) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f784,f414])).

fof(f784,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f783,f416])).

fof(f783,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f782,f414])).

fof(f782,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f781])).

fof(f781,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f780,f414])).

fof(f780,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f779,f79])).

fof(f779,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f778,f80])).

fof(f778,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f777,f81])).

fof(f777,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f776,f84])).

fof(f84,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f776,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f775,f163])).

fof(f775,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f774,f166])).

fof(f774,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f773,f86])).

fof(f773,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f772,f82])).

fof(f772,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK2,sK3)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f748,f382])).

fof(f748,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1)
        | r1_tmap_1(sK3,sK1,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_pre_topc(sK2,sK3)
        | ~ v1_tsep_1(sK2,sK3)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl7_2 ),
    inference(superposition,[],[f129,f702])).

fof(f702,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f697,f680])).

fof(f697,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f666,f382])).

fof(f666,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f221,f414])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f220,f84])).

fof(f220,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f219,f163])).

fof(f219,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f218,f166])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f217,f79])).

fof(f217,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f216,f80])).

fof(f216,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f215,f81])).

fof(f215,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f214,f86])).

fof(f214,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f212,f87])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f88,f112])).

fof(f129,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f343,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f341,f151])).

fof(f341,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_1 ),
    inference(resolution,[],[f197,f100])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f197,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl7_1
  <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f201,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f187,f199,f195])).

fof(f187,plain,(
    ! [X6,X7] :
      ( sK3 != g1_pre_topc(X6,X7)
      | u1_struct_0(sK2) = X6
      | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(superposition,[],[f124,f89])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (28405)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (28413)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28415)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (28407)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (28397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (28395)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (28394)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28393)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (28404)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (28398)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (28417)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (28400)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (28418)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (28409)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (28411)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (28408)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (28410)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (28396)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (28401)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (28406)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (28402)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (28416)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (28403)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (28398)Refutation not found, incomplete strategy% (28398)------------------------------
% 0.21/0.56  % (28398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28398)Memory used [KB]: 6396
% 0.21/0.56  % (28398)Time elapsed: 0.128 s
% 0.21/0.56  % (28398)------------------------------
% 0.21/0.56  % (28398)------------------------------
% 0.21/0.56  % (28393)Refutation not found, incomplete strategy% (28393)------------------------------
% 0.21/0.56  % (28393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28393)Memory used [KB]: 10874
% 0.21/0.56  % (28393)Time elapsed: 0.147 s
% 0.21/0.56  % (28393)------------------------------
% 0.21/0.56  % (28393)------------------------------
% 0.21/0.56  % (28399)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (28412)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (28414)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.89/0.60  % (28400)Refutation not found, incomplete strategy% (28400)------------------------------
% 1.89/0.60  % (28400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.60  % (28400)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.60  
% 1.89/0.60  % (28400)Memory used [KB]: 2046
% 1.89/0.60  % (28400)Time elapsed: 0.158 s
% 1.89/0.60  % (28400)------------------------------
% 1.89/0.60  % (28400)------------------------------
% 1.89/0.61  % (28394)Refutation found. Thanks to Tanya!
% 1.89/0.61  % SZS status Theorem for theBenchmark
% 1.89/0.61  % SZS output start Proof for theBenchmark
% 1.89/0.61  fof(f1761,plain,(
% 1.89/0.61    $false),
% 1.89/0.61    inference(avatar_sat_refutation,[],[f201,f343,f790,f1108,f1749])).
% 1.89/0.61  fof(f1749,plain,(
% 1.89/0.61    ~spl7_2 | ~spl7_25),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f1748])).
% 1.89/0.61  fof(f1748,plain,(
% 1.89/0.61    $false | (~spl7_2 | ~spl7_25)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1747,f173])).
% 1.89/0.61  fof(f173,plain,(
% 1.89/0.61    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.89/0.61    inference(forward_demodulation,[],[f91,f92])).
% 1.89/0.61  fof(f92,plain,(
% 1.89/0.61    sK5 = sK6),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f67,plain,(
% 1.89/0.61    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.89/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f28,f66,f65,f64,f63,f62,f61,f60])).
% 1.89/0.61  fof(f60,plain,(
% 1.89/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f61,plain,(
% 1.89/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f62,plain,(
% 1.89/0.61    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f63,plain,(
% 1.89/0.61    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f64,plain,(
% 1.89/0.61    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f65,plain,(
% 1.89/0.61    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f66,plain,(
% 1.89/0.61    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.89/0.61    introduced(choice_axiom,[])).
% 1.89/0.61  fof(f28,plain,(
% 1.89/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/0.61    inference(flattening,[],[f27])).
% 1.89/0.61  fof(f27,plain,(
% 1.89/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f26])).
% 1.89/0.61  fof(f26,negated_conjecture,(
% 1.89/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.89/0.61    inference(negated_conjecture,[],[f25])).
% 1.89/0.61  fof(f25,conjecture,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.89/0.61  fof(f91,plain,(
% 1.89/0.61    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f1747,plain,(
% 1.89/0.61    ~m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl7_2 | ~spl7_25)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1742,f94])).
% 1.89/0.61  fof(f94,plain,(
% 1.89/0.61    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f1742,plain,(
% 1.89/0.61    r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl7_2 | ~spl7_25)),
% 1.89/0.61    inference(resolution,[],[f789,f1061])).
% 1.89/0.61  fof(f1061,plain,(
% 1.89/0.61    r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),sK5) | ~spl7_2),
% 1.89/0.61    inference(backward_demodulation,[],[f231,f1058])).
% 1.89/0.61  fof(f1058,plain,(
% 1.89/0.61    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_tmap_1(sK2,sK1,sK4,sK2) | ~spl7_2),
% 1.89/0.61    inference(forward_demodulation,[],[f1052,f680])).
% 1.89/0.61  fof(f680,plain,(
% 1.89/0.61    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f675,f151])).
% 1.89/0.61  fof(f151,plain,(
% 1.89/0.61    l1_pre_topc(sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f144,f78])).
% 1.89/0.61  fof(f78,plain,(
% 1.89/0.61    l1_pre_topc(sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f144,plain,(
% 1.89/0.61    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.89/0.61    inference(resolution,[],[f83,f104])).
% 1.89/0.61  fof(f104,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f36])).
% 1.89/0.61  fof(f36,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f9])).
% 1.89/0.61  fof(f9,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.89/0.61  fof(f83,plain,(
% 1.89/0.61    m1_pre_topc(sK2,sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f675,plain,(
% 1.89/0.61    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~spl7_2),
% 1.89/0.61    inference(resolution,[],[f483,f99])).
% 1.89/0.61  fof(f99,plain,(
% 1.89/0.61    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f31])).
% 1.89/0.61  fof(f31,plain,(
% 1.89/0.61    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f21])).
% 1.89/0.61  fof(f21,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.89/0.61  fof(f483,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f482,f82])).
% 1.89/0.61  fof(f82,plain,(
% 1.89/0.61    ~v2_struct_0(sK2)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f482,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f481,f148])).
% 1.89/0.61  fof(f148,plain,(
% 1.89/0.61    v2_pre_topc(sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f147,f77])).
% 1.89/0.61  fof(f77,plain,(
% 1.89/0.61    v2_pre_topc(sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f147,plain,(
% 1.89/0.61    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 1.89/0.61    inference(subsumption_resolution,[],[f141,f78])).
% 1.89/0.61  fof(f141,plain,(
% 1.89/0.61    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.89/0.61    inference(resolution,[],[f83,f117])).
% 1.89/0.61  fof(f117,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f52])).
% 1.89/0.61  fof(f52,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f51])).
% 1.89/0.61  fof(f51,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f5])).
% 1.89/0.61  fof(f5,axiom,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.89/0.61  fof(f481,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f480,f151])).
% 1.89/0.61  fof(f480,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f479,f79])).
% 1.89/0.61  fof(f79,plain,(
% 1.89/0.61    ~v2_struct_0(sK1)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f479,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f478,f80])).
% 1.89/0.61  fof(f80,plain,(
% 1.89/0.61    v2_pre_topc(sK1)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f478,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f477,f81])).
% 1.89/0.61  fof(f81,plain,(
% 1.89/0.61    l1_pre_topc(sK1)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f477,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f476,f86])).
% 1.89/0.61  fof(f86,plain,(
% 1.89/0.61    v1_funct_1(sK4)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f476,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f474,f415])).
% 1.89/0.61  fof(f415,plain,(
% 1.89/0.61    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl7_2),
% 1.89/0.61    inference(backward_demodulation,[],[f87,f414])).
% 1.89/0.61  fof(f414,plain,(
% 1.89/0.61    u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl7_2),
% 1.89/0.61    inference(trivial_inequality_removal,[],[f413])).
% 1.89/0.61  fof(f413,plain,(
% 1.89/0.61    sK3 != sK3 | u1_struct_0(sK2) = u1_struct_0(sK3) | ~spl7_2),
% 1.89/0.61    inference(superposition,[],[f200,f230])).
% 1.89/0.61  fof(f230,plain,(
% 1.89/0.61    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 1.89/0.61    inference(subsumption_resolution,[],[f229,f166])).
% 1.89/0.61  fof(f166,plain,(
% 1.89/0.61    l1_pre_topc(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f159,f78])).
% 1.89/0.61  fof(f159,plain,(
% 1.89/0.61    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.89/0.61    inference(resolution,[],[f85,f104])).
% 1.89/0.61  fof(f85,plain,(
% 1.89/0.61    m1_pre_topc(sK3,sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f229,plain,(
% 1.89/0.61    sK3 = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~l1_pre_topc(sK3)),
% 1.89/0.61    inference(resolution,[],[f228,f101])).
% 1.89/0.61  fof(f101,plain,(
% 1.89/0.61    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f34])).
% 1.89/0.61  fof(f34,plain,(
% 1.89/0.61    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f33])).
% 1.89/0.61  fof(f33,plain,(
% 1.89/0.61    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f4])).
% 1.89/0.61  fof(f4,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.89/0.61  fof(f228,plain,(
% 1.89/0.61    v1_pre_topc(sK3)),
% 1.89/0.61    inference(forward_demodulation,[],[f149,f89])).
% 1.89/0.61  fof(f89,plain,(
% 1.89/0.61    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f149,plain,(
% 1.89/0.61    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.89/0.61    inference(subsumption_resolution,[],[f142,f78])).
% 1.89/0.61  fof(f142,plain,(
% 1.89/0.61    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK0)),
% 1.89/0.61    inference(resolution,[],[f83,f106])).
% 1.89/0.61  fof(f106,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f38])).
% 1.89/0.61  fof(f38,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f18])).
% 1.89/0.61  fof(f18,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.89/0.61  fof(f200,plain,(
% 1.89/0.61    ( ! [X6,X7] : (sK3 != g1_pre_topc(X6,X7) | u1_struct_0(sK2) = X6) ) | ~spl7_2),
% 1.89/0.61    inference(avatar_component_clause,[],[f199])).
% 1.89/0.61  fof(f199,plain,(
% 1.89/0.61    spl7_2 <=> ! [X7,X6] : (sK3 != g1_pre_topc(X6,X7) | u1_struct_0(sK2) = X6)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.89/0.61  fof(f87,plain,(
% 1.89/0.61    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f474,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl7_2),
% 1.89/0.61    inference(resolution,[],[f416,f112])).
% 1.89/0.61  fof(f112,plain,(
% 1.89/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f44])).
% 1.89/0.61  fof(f44,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.89/0.61    inference(flattening,[],[f43])).
% 1.89/0.61  fof(f43,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f16])).
% 1.89/0.61  fof(f16,axiom,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.89/0.61  fof(f416,plain,(
% 1.89/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~spl7_2),
% 1.89/0.61    inference(backward_demodulation,[],[f88,f414])).
% 1.89/0.61  fof(f88,plain,(
% 1.89/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f1052,plain,(
% 1.89/0.61    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) | ~spl7_2),
% 1.89/0.61    inference(resolution,[],[f851,f382])).
% 1.89/0.61  fof(f382,plain,(
% 1.89/0.61    m1_pre_topc(sK2,sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f381,f151])).
% 1.89/0.61  fof(f381,plain,(
% 1.89/0.61    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.89/0.61    inference(duplicate_literal_removal,[],[f378])).
% 1.89/0.61  fof(f378,plain,(
% 1.89/0.61    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 1.89/0.61    inference(resolution,[],[f191,f99])).
% 1.89/0.61  fof(f191,plain,(
% 1.89/0.61    ( ! [X2] : (~m1_pre_topc(X2,sK2) | m1_pre_topc(X2,sK3) | ~l1_pre_topc(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f184,f151])).
% 1.89/0.61  fof(f184,plain,(
% 1.89/0.61    ( ! [X2] : (m1_pre_topc(X2,sK3) | ~m1_pre_topc(X2,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X2)) )),
% 1.89/0.61    inference(superposition,[],[f102,f89])).
% 1.89/0.61  fof(f102,plain,(
% 1.89/0.61    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f68])).
% 1.89/0.61  fof(f68,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(nnf_transformation,[],[f35])).
% 1.89/0.61  fof(f35,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f14])).
% 1.89/0.61  fof(f14,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.89/0.61  fof(f851,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f850,f76])).
% 1.89/0.61  fof(f76,plain,(
% 1.89/0.61    ~v2_struct_0(sK0)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f850,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f849,f77])).
% 1.89/0.61  fof(f849,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f844,f78])).
% 1.89/0.61  fof(f844,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_2),
% 1.89/0.61    inference(resolution,[],[f791,f85])).
% 1.89/0.61  fof(f791,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl7_2),
% 1.89/0.61    inference(forward_demodulation,[],[f227,f414])).
% 1.89/0.61  fof(f227,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f226,f118])).
% 1.89/0.61  fof(f118,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f54])).
% 1.89/0.61  fof(f54,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f53])).
% 1.89/0.61  fof(f53,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f24])).
% 1.89/0.61  fof(f24,axiom,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.89/0.61  fof(f226,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f225,f79])).
% 1.89/0.61  fof(f225,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f224,f80])).
% 1.89/0.61  fof(f224,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f223,f81])).
% 1.89/0.61  fof(f223,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f222,f86])).
% 1.89/0.61  fof(f222,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f213,f87])).
% 1.89/0.61  fof(f213,plain,(
% 1.89/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(X2,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.89/0.61    inference(resolution,[],[f88,f111])).
% 1.89/0.61  fof(f111,plain,(
% 1.89/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f42])).
% 1.89/0.61  fof(f42,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.89/0.61    inference(flattening,[],[f41])).
% 1.89/0.61  fof(f41,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f17])).
% 1.89/0.61  fof(f17,axiom,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.89/0.61  fof(f231,plain,(
% 1.89/0.61    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.89/0.61    inference(forward_demodulation,[],[f93,f92])).
% 1.89/0.61  fof(f93,plain,(
% 1.89/0.61    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.89/0.61    inference(cnf_transformation,[],[f67])).
% 1.89/0.61  fof(f789,plain,(
% 1.89/0.61    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | ~spl7_25),
% 1.89/0.61    inference(avatar_component_clause,[],[f788])).
% 1.89/0.61  fof(f788,plain,(
% 1.89/0.61    spl7_25 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | r1_tmap_1(sK3,sK1,sK4,X1) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1))),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.89/0.61  fof(f1108,plain,(
% 1.89/0.61    ~spl7_2 | spl7_23),
% 1.89/0.61    inference(avatar_contradiction_clause,[],[f1107])).
% 1.89/0.61  fof(f1107,plain,(
% 1.89/0.61    $false | (~spl7_2 | spl7_23)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1106,f382])).
% 1.89/0.61  fof(f1106,plain,(
% 1.89/0.61    ~m1_pre_topc(sK2,sK3) | (~spl7_2 | spl7_23)),
% 1.89/0.61    inference(subsumption_resolution,[],[f1105,f767])).
% 1.89/0.61  fof(f767,plain,(
% 1.89/0.61    ~v1_tsep_1(sK2,sK3) | spl7_23),
% 1.89/0.61    inference(avatar_component_clause,[],[f765])).
% 1.89/0.61  fof(f765,plain,(
% 1.89/0.61    spl7_23 <=> v1_tsep_1(sK2,sK3)),
% 1.89/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.89/0.61  fof(f1105,plain,(
% 1.89/0.61    v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f1103,f420])).
% 1.89/0.61  fof(f420,plain,(
% 1.89/0.61    v3_pre_topc(u1_struct_0(sK2),sK3) | ~spl7_2),
% 1.89/0.61    inference(backward_demodulation,[],[f211,f414])).
% 1.89/0.61  fof(f211,plain,(
% 1.89/0.61    v3_pre_topc(u1_struct_0(sK3),sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f210,f163])).
% 1.89/0.61  fof(f163,plain,(
% 1.89/0.61    v2_pre_topc(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f162,f77])).
% 1.89/0.61  fof(f162,plain,(
% 1.89/0.61    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 1.89/0.61    inference(subsumption_resolution,[],[f156,f78])).
% 1.89/0.61  fof(f156,plain,(
% 1.89/0.61    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.89/0.61    inference(resolution,[],[f85,f117])).
% 1.89/0.61  fof(f210,plain,(
% 1.89/0.61    v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.89/0.61    inference(subsumption_resolution,[],[f209,f166])).
% 1.89/0.61  fof(f209,plain,(
% 1.89/0.61    v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.89/0.61    inference(superposition,[],[f116,f170])).
% 1.89/0.61  fof(f170,plain,(
% 1.89/0.61    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.89/0.61    inference(resolution,[],[f168,f97])).
% 1.89/0.61  fof(f97,plain,(
% 1.89/0.61    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f29])).
% 1.89/0.61  fof(f29,plain,(
% 1.89/0.61    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f6])).
% 1.89/0.61  fof(f6,axiom,(
% 1.89/0.61    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.89/0.61  fof(f168,plain,(
% 1.89/0.61    l1_struct_0(sK3)),
% 1.89/0.61    inference(resolution,[],[f166,f98])).
% 1.89/0.61  fof(f98,plain,(
% 1.89/0.61    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f30])).
% 1.89/0.61  fof(f30,plain,(
% 1.89/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f8])).
% 1.89/0.61  fof(f8,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.89/0.61  fof(f116,plain,(
% 1.89/0.61    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f50])).
% 1.89/0.61  fof(f50,plain,(
% 1.89/0.61    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f49])).
% 1.89/0.61  fof(f49,plain,(
% 1.89/0.61    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.61    inference(ennf_transformation,[],[f15])).
% 1.89/0.61  fof(f15,axiom,(
% 1.89/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.89/0.61  fof(f1103,plain,(
% 1.89/0.61    ~v3_pre_topc(u1_struct_0(sK2),sK3) | v1_tsep_1(sK2,sK3) | ~m1_pre_topc(sK2,sK3) | ~spl7_2),
% 1.89/0.61    inference(resolution,[],[f467,f424])).
% 1.89/0.61  fof(f424,plain,(
% 1.89/0.61    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl7_2),
% 1.89/0.61    inference(backward_demodulation,[],[f312,f414])).
% 1.89/0.61  fof(f312,plain,(
% 1.89/0.61    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.89/0.61    inference(subsumption_resolution,[],[f306,f151])).
% 1.89/0.61  fof(f306,plain,(
% 1.89/0.61    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.89/0.61    inference(resolution,[],[f300,f105])).
% 1.89/0.61  fof(f105,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f37])).
% 1.89/0.61  fof(f37,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f20])).
% 1.89/0.61  fof(f20,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.89/0.61  fof(f300,plain,(
% 1.89/0.61    m1_pre_topc(sK3,sK2)),
% 1.89/0.61    inference(subsumption_resolution,[],[f298,f166])).
% 1.89/0.61  fof(f298,plain,(
% 1.89/0.61    m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK3)),
% 1.89/0.61    inference(resolution,[],[f190,f99])).
% 1.89/0.61  fof(f190,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK2)) )),
% 1.89/0.61    inference(subsumption_resolution,[],[f182,f151])).
% 1.89/0.61  fof(f182,plain,(
% 1.89/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 1.89/0.61    inference(superposition,[],[f110,f89])).
% 1.89/0.61  fof(f110,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f40])).
% 1.89/0.61  fof(f40,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.61    inference(ennf_transformation,[],[f13])).
% 1.89/0.61  fof(f13,axiom,(
% 1.89/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.89/0.61  fof(f467,plain,(
% 1.89/0.61    ( ! [X26] : (~m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(u1_struct_0(X26),sK3) | v1_tsep_1(X26,sK3) | ~m1_pre_topc(X26,sK3)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f466,f163])).
% 1.89/0.61  fof(f466,plain,(
% 1.89/0.61    ( ! [X26] : (~m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(u1_struct_0(X26),sK3) | v1_tsep_1(X26,sK3) | ~m1_pre_topc(X26,sK3) | ~v2_pre_topc(sK3)) ) | ~spl7_2),
% 1.89/0.61    inference(subsumption_resolution,[],[f442,f166])).
% 1.89/0.61  fof(f442,plain,(
% 1.89/0.61    ( ! [X26] : (~m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(u1_struct_0(X26),sK3) | v1_tsep_1(X26,sK3) | ~m1_pre_topc(X26,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)) ) | ~spl7_2),
% 1.89/0.61    inference(superposition,[],[f132,f414])).
% 1.89/0.61  fof(f132,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.61    inference(equality_resolution,[],[f122])).
% 1.89/0.61  fof(f122,plain,(
% 1.89/0.61    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f73])).
% 1.89/0.61  fof(f73,plain,(
% 1.89/0.61    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.61    inference(flattening,[],[f72])).
% 1.89/0.62  fof(f72,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f58])).
% 1.89/0.62  fof(f58,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.89/0.62    inference(flattening,[],[f57])).
% 1.89/0.62  fof(f57,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,axiom,(
% 1.89/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.89/0.62  fof(f790,plain,(
% 1.89/0.62    ~spl7_23 | spl7_25 | ~spl7_2),
% 1.89/0.62    inference(avatar_split_clause,[],[f786,f199,f788,f765])).
% 1.89/0.62  fof(f786,plain,(
% 1.89/0.62    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~v1_tsep_1(sK2,sK3)) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f785,f415])).
% 1.89/0.62  fof(f785,plain,(
% 1.89/0.62    ( ! [X1] : (~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~v1_tsep_1(sK2,sK3)) ) | ~spl7_2),
% 1.89/0.62    inference(forward_demodulation,[],[f784,f414])).
% 1.89/0.62  fof(f784,plain,(
% 1.89/0.62    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~v1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f783,f416])).
% 1.89/0.62  fof(f783,plain,(
% 1.89/0.62    ( ! [X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~v1_tsep_1(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl7_2),
% 1.89/0.62    inference(forward_demodulation,[],[f782,f414])).
% 1.89/0.62  fof(f782,plain,(
% 1.89/0.62    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl7_2),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f781])).
% 1.89/0.62  fof(f781,plain,(
% 1.89/0.62    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl7_2),
% 1.89/0.62    inference(forward_demodulation,[],[f780,f414])).
% 1.89/0.62  fof(f780,plain,(
% 1.89/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f779,f79])).
% 1.89/0.62  fof(f779,plain,(
% 1.89/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1)) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f778,f80])).
% 1.89/0.62  fof(f778,plain,(
% 1.89/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f777,f81])).
% 1.89/0.62  fof(f777,plain,(
% 1.89/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f776,f84])).
% 1.89/0.62  fof(f84,plain,(
% 1.89/0.62    ~v2_struct_0(sK3)),
% 1.89/0.62    inference(cnf_transformation,[],[f67])).
% 1.89/0.62  fof(f776,plain,(
% 1.89/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 1.89/0.62    inference(subsumption_resolution,[],[f775,f163])).
% 2.12/0.62  fof(f775,plain,(
% 2.12/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 2.12/0.62    inference(subsumption_resolution,[],[f774,f166])).
% 2.12/0.62  fof(f774,plain,(
% 2.12/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 2.12/0.62    inference(subsumption_resolution,[],[f773,f86])).
% 2.12/0.62  fof(f773,plain,(
% 2.12/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 2.12/0.62    inference(subsumption_resolution,[],[f772,f82])).
% 2.12/0.62  fof(f772,plain,(
% 2.12/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 2.12/0.62    inference(subsumption_resolution,[],[f748,f382])).
% 2.12/0.62  fof(f748,plain,(
% 2.12/0.62    ( ! [X1] : (~r1_tmap_1(sK2,sK1,k2_tmap_1(sK2,sK1,sK4,sK2),X1) | r1_tmap_1(sK3,sK1,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl7_2),
% 2.12/0.62    inference(superposition,[],[f129,f702])).
% 2.12/0.62  fof(f702,plain,(
% 2.12/0.62    k2_tmap_1(sK2,sK1,sK4,sK2) = k2_tmap_1(sK3,sK1,sK4,sK2) | ~spl7_2),
% 2.12/0.62    inference(forward_demodulation,[],[f697,f680])).
% 2.12/0.62  fof(f697,plain,(
% 2.12/0.62    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK3,sK1,sK4,sK2) | ~spl7_2),
% 2.12/0.62    inference(resolution,[],[f666,f382])).
% 2.12/0.62  fof(f666,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(X0))) ) | ~spl7_2),
% 2.12/0.62    inference(forward_demodulation,[],[f221,f414])).
% 2.12/0.62  fof(f221,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0))) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f220,f84])).
% 2.12/0.62  fof(f220,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f219,f163])).
% 2.12/0.62  fof(f219,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f218,f166])).
% 2.12/0.62  fof(f218,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f217,f79])).
% 2.12/0.62  fof(f217,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f216,f80])).
% 2.12/0.62  fof(f216,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f215,f81])).
% 2.12/0.62  fof(f215,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f214,f86])).
% 2.12/0.62  fof(f214,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(subsumption_resolution,[],[f212,f87])).
% 2.12/0.62  fof(f212,plain,(
% 2.12/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK1,sK4,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 2.12/0.62    inference(resolution,[],[f88,f112])).
% 2.12/0.62  fof(f129,plain,(
% 2.12/0.62    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.12/0.62    inference(equality_resolution,[],[f114])).
% 2.12/0.62  fof(f114,plain,(
% 2.12/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.12/0.62    inference(cnf_transformation,[],[f70])).
% 2.12/0.62  fof(f70,plain,(
% 2.12/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.12/0.62    inference(nnf_transformation,[],[f46])).
% 2.12/0.62  fof(f46,plain,(
% 2.12/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.12/0.62    inference(flattening,[],[f45])).
% 2.12/0.62  fof(f45,plain,(
% 2.12/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.12/0.62    inference(ennf_transformation,[],[f23])).
% 2.12/0.62  fof(f23,axiom,(
% 2.12/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.12/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 2.12/0.62  fof(f343,plain,(
% 2.12/0.62    spl7_1),
% 2.12/0.62    inference(avatar_contradiction_clause,[],[f342])).
% 2.12/0.62  fof(f342,plain,(
% 2.12/0.62    $false | spl7_1),
% 2.12/0.62    inference(subsumption_resolution,[],[f341,f151])).
% 2.12/0.62  fof(f341,plain,(
% 2.12/0.62    ~l1_pre_topc(sK2) | spl7_1),
% 2.12/0.62    inference(resolution,[],[f197,f100])).
% 2.12/0.62  fof(f100,plain,(
% 2.12/0.62    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.12/0.62    inference(cnf_transformation,[],[f32])).
% 2.12/0.62  fof(f32,plain,(
% 2.12/0.62    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.62    inference(ennf_transformation,[],[f10])).
% 2.12/0.62  fof(f10,axiom,(
% 2.12/0.62    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.12/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 2.12/0.62  fof(f197,plain,(
% 2.12/0.62    ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | spl7_1),
% 2.12/0.62    inference(avatar_component_clause,[],[f195])).
% 2.12/0.62  fof(f195,plain,(
% 2.12/0.62    spl7_1 <=> m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 2.12/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.12/0.62  fof(f201,plain,(
% 2.12/0.62    ~spl7_1 | spl7_2),
% 2.12/0.62    inference(avatar_split_clause,[],[f187,f199,f195])).
% 2.12/0.62  fof(f187,plain,(
% 2.12/0.62    ( ! [X6,X7] : (sK3 != g1_pre_topc(X6,X7) | u1_struct_0(sK2) = X6 | ~m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) )),
% 2.12/0.62    inference(superposition,[],[f124,f89])).
% 2.12/0.62  fof(f124,plain,(
% 2.12/0.62    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.12/0.62    inference(cnf_transformation,[],[f59])).
% 2.12/0.62  fof(f59,plain,(
% 2.12/0.62    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.12/0.62    inference(ennf_transformation,[],[f11])).
% 2.12/0.62  fof(f11,axiom,(
% 2.12/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.12/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 2.12/0.62  % SZS output end Proof for theBenchmark
% 2.12/0.62  % (28394)------------------------------
% 2.12/0.62  % (28394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.62  % (28394)Termination reason: Refutation
% 2.12/0.62  
% 2.12/0.62  % (28394)Memory used [KB]: 11385
% 2.12/0.62  % (28394)Time elapsed: 0.189 s
% 2.12/0.62  % (28394)------------------------------
% 2.12/0.62  % (28394)------------------------------
% 2.12/0.63  % (28392)Success in time 0.27 s
%------------------------------------------------------------------------------
