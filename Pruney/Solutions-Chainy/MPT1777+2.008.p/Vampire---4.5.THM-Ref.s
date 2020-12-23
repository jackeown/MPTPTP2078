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
% DateTime   : Thu Dec  3 13:19:02 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  216 (2967 expanded)
%              Number of leaves         :   31 (1532 expanded)
%              Depth                    :   47
%              Number of atoms          : 1314 (46653 expanded)
%              Number of equality atoms :  115 (6282 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f280,f399,f407,f495,f1273])).

fof(f1273,plain,
    ( ~ spl11_2
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f1272])).

fof(f1272,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f1271,f94])).

fof(f94,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
    & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f59,f58,f57,f56,f55,f54,f53])).

fof(f53,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK2,X4,X5)
                          & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK2,X4,X5)
                        & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK2,X4,X5)
                      & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK3)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK2,X4,X5)
                    & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK3)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK4,sK2,X4,X5)
                  & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,u1_struct_0(sK4)) )
          & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
          & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK4,sK2,X4,X5)
                & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,u1_struct_0(sK4)) )
        & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK4,sK2,sK5,X5)
              & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,u1_struct_0(sK4)) )
      & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
      & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK4,sK2,sK5,X5)
            & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,u1_struct_0(sK4)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
          & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6)
          & sK6 = X6
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
        & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6)
        & sK6 = X6
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ~ r1_tmap_1(sK4,sK2,sK5,sK6)
      & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)
      & sK6 = sK7
      & m1_subset_1(sK7,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f1271,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f1266,f168])).

fof(f168,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1266,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(resolution,[],[f740,f1027])).

fof(f1027,plain,
    ( r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),sK6)
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f239,f1024])).

fof(f1024,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK3,sK2,sK5,sK3)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f1018,f650])).

fof(f650,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f646,f151])).

fof(f151,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f146,f78])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f146,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f83,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f83,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f646,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f487,f97])).

fof(f97,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f487,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f486,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f486,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f485,f148])).

fof(f148,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f147,f77])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f147,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f143,f78])).

fof(f143,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f83,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f485,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f484,f151])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f483,f79])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f482,f80])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f481,f81])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f480,f86])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f478,f411])).

fof(f411,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f87,f410])).

fof(f410,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl11_2 ),
    inference(trivial_inequality_removal,[],[f409])).

fof(f409,plain,
    ( sK4 != sK4
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl11_2 ),
    inference(superposition,[],[f186,f194])).

fof(f194,plain,(
    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f193,f163])).

fof(f163,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f158,f78])).

fof(f158,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f85,f114])).

fof(f85,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f193,plain,
    ( sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f192,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f192,plain,(
    v1_pre_topc(sK4) ),
    inference(forward_demodulation,[],[f149,f89])).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f60])).

fof(f149,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f144,f78])).

fof(f144,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f83,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f186,plain,
    ( ! [X6,X5] :
        ( sK4 != g1_pre_topc(X5,X6)
        | u1_struct_0(sK3) = X5 )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl11_2
  <=> ! [X5,X6] :
        ( sK4 != g1_pre_topc(X5,X6)
        | u1_struct_0(sK3) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f87,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f478,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(resolution,[],[f412,f121])).

fof(f121,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f412,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f88,f410])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f1018,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ spl11_2 ),
    inference(resolution,[],[f841,f364])).

fof(f364,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(subsumption_resolution,[],[f363,f151])).

fof(f363,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f178,f97])).

fof(f178,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK4)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f172,f151])).

fof(f172,plain,(
    ! [X1] :
      ( m1_pre_topc(X1,sK4)
      | ~ m1_pre_topc(X1,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f112,f89])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f841,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f840,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f839,f77])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f834,f78])).

fof(f834,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(resolution,[],[f741,f85])).

fof(f741,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(sK4,X2)
        | ~ m1_pre_topc(X1,sK4)
        | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X1))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f238,f410])).

fof(f238,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f237,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
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
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f237,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f236,f79])).

fof(f236,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f235,f80])).

fof(f235,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f234,f81])).

fof(f234,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f233,f86])).

fof(f233,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f224,f87])).

fof(f224,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f88,f120])).

fof(f120,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f239,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(forward_demodulation,[],[f93,f92])).

fof(f93,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f740,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r1_tmap_1(sK4,sK2,sK5,X1) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f739,f411])).

fof(f739,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f738,f410])).

fof(f738,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f737,f412])).

fof(f737,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f736,f410])).

fof(f736,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(duplicate_literal_removal,[],[f735])).

fof(f735,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f734,f410])).

fof(f734,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f733,f79])).

fof(f733,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f732,f80])).

fof(f732,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f731,f81])).

fof(f731,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f730,f84])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f730,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f729,f160])).

fof(f160,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f159,f77])).

fof(f159,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f155,f78])).

fof(f155,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f85,f125])).

fof(f729,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f728,f163])).

fof(f728,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f727,f86])).

fof(f727,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f726,f82])).

fof(f726,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f725,f393])).

fof(f393,plain,
    ( v1_tsep_1(sK3,sK4)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl11_21
  <=> v1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f725,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ v1_tsep_1(sK3,sK4)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f708,f364])).

fof(f708,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK3,sK4)
        | ~ v1_tsep_1(sK3,sK4)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(superposition,[],[f132,f662])).

fof(f662,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f657,f650])).

fof(f657,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f632,f364])).

fof(f632,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f232,f410])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f231,f84])).

fof(f231,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f230,f160])).

fof(f230,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f229,f163])).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f228,f79])).

fof(f228,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f227,f80])).

fof(f227,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f226,f81])).

fof(f226,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f225,f86])).

fof(f225,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f223,f87])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f88,f121])).

fof(f132,plain,(
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
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f495,plain,
    ( ~ spl11_2
    | spl11_22 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl11_2
    | spl11_22 ),
    inference(subsumption_resolution,[],[f449,f403])).

fof(f403,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | spl11_22 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl11_22
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f449,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f448,f163])).

fof(f448,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f427,f160])).

fof(f427,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl11_2 ),
    inference(superposition,[],[f106,f410])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
            & r1_tarski(sK10(X0),u1_pre_topc(X0))
            & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f68,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r1_tarski(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f30,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f407,plain,
    ( spl11_20
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f406,f402,f388])).

fof(f388,plain,
    ( spl11_20
  <=> v3_pre_topc(u1_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f406,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | v3_pre_topc(u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f383,f163])).

fof(f383,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f374,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f374,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f370,f163])).

fof(f370,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f364,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f399,plain,
    ( spl11_21
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f398,f388,f392])).

fof(f398,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f397,f160])).

fof(f397,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK3,sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f396,f163])).

fof(f396,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f381,f364])).

fof(f381,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(resolution,[],[f374,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f280,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f278,f151])).

fof(f278,plain,
    ( ~ l1_pre_topc(sK3)
    | spl11_1 ),
    inference(resolution,[],[f183,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f183,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl11_1
  <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f187,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f175,f185,f181])).

fof(f175,plain,(
    ! [X6,X5] :
      ( sK4 != g1_pre_topc(X5,X6)
      | u1_struct_0(sK3) = X5
      | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ) ),
    inference(superposition,[],[f130,f89])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (31092)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.46  % (31104)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.46  % (31092)Refutation not found, incomplete strategy% (31092)------------------------------
% 0.19/0.46  % (31092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (31100)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.47  % (31092)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (31092)Memory used [KB]: 6396
% 0.19/0.47  % (31092)Time elapsed: 0.078 s
% 0.19/0.47  % (31092)------------------------------
% 0.19/0.47  % (31092)------------------------------
% 0.19/0.48  % (31091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (31105)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.48  % (31096)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (31095)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.49  % (31103)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.49  % (31090)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (31087)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (31099)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (31088)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (31101)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (31089)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.51  % (31112)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.51  % (31109)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (31113)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.51  % (31107)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (31110)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.51  % (31102)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (31111)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.51  % (31098)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (31097)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.52  % (31106)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.52  % (31094)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.32/0.53  % (31087)Refutation not found, incomplete strategy% (31087)------------------------------
% 1.32/0.53  % (31087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (31095)Refutation not found, incomplete strategy% (31095)------------------------------
% 1.32/0.53  % (31095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (31087)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (31087)Memory used [KB]: 10874
% 1.32/0.53  % (31087)Time elapsed: 0.129 s
% 1.32/0.53  % (31087)------------------------------
% 1.32/0.53  % (31087)------------------------------
% 1.32/0.53  % (31095)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (31095)Memory used [KB]: 2046
% 1.32/0.53  % (31095)Time elapsed: 0.125 s
% 1.32/0.53  % (31095)------------------------------
% 1.32/0.53  % (31095)------------------------------
% 1.44/0.55  % (31108)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.44/0.55  % (31088)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f1285,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f187,f280,f399,f407,f495,f1273])).
% 1.44/0.55  fof(f1273,plain,(
% 1.44/0.55    ~spl11_2 | ~spl11_21),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f1272])).
% 1.44/0.55  fof(f1272,plain,(
% 1.44/0.55    $false | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f1271,f94])).
% 1.44/0.55  fof(f94,plain,(
% 1.44/0.55    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f60,plain,(
% 1.44/0.55    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f59,f58,f57,f56,f55,f54,f53])).
% 1.44/0.55  fof(f53,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f54,plain,(
% 1.44/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f55,plain,(
% 1.44/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    ? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) => (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f59,plain,(
% 1.44/0.55    ? [X6] : (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) => (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3)))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f23])).
% 1.44/0.55  fof(f23,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,negated_conjecture,(
% 1.44/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.44/0.55    inference(negated_conjecture,[],[f20])).
% 1.44/0.55  fof(f20,conjecture,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.44/0.55  fof(f1271,plain,(
% 1.44/0.55    r1_tmap_1(sK4,sK2,sK5,sK6) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f1266,f168])).
% 1.44/0.55  fof(f168,plain,(
% 1.44/0.55    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.44/0.55    inference(forward_demodulation,[],[f91,f92])).
% 1.44/0.55  fof(f92,plain,(
% 1.44/0.55    sK6 = sK7),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f91,plain,(
% 1.44/0.55    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f1266,plain,(
% 1.44/0.55    ~m1_subset_1(sK6,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,sK5,sK6) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(resolution,[],[f740,f1027])).
% 1.44/0.55  fof(f1027,plain,(
% 1.44/0.55    r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),sK6) | ~spl11_2),
% 1.44/0.55    inference(backward_demodulation,[],[f239,f1024])).
% 1.44/0.55  fof(f1024,plain,(
% 1.44/0.55    k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK3,sK2,sK5,sK3) | ~spl11_2),
% 1.44/0.55    inference(forward_demodulation,[],[f1018,f650])).
% 1.44/0.55  fof(f650,plain,(
% 1.44/0.55    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f646,f151])).
% 1.44/0.55  fof(f151,plain,(
% 1.44/0.55    l1_pre_topc(sK3)),
% 1.44/0.55    inference(subsumption_resolution,[],[f146,f78])).
% 1.44/0.55  fof(f78,plain,(
% 1.44/0.55    l1_pre_topc(sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f146,plain,(
% 1.44/0.55    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 1.44/0.55    inference(resolution,[],[f83,f114])).
% 1.44/0.55  fof(f114,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f7])).
% 1.44/0.55  fof(f7,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    m1_pre_topc(sK3,sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f646,plain,(
% 1.44/0.55    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~spl11_2),
% 1.44/0.55    inference(resolution,[],[f487,f97])).
% 1.44/0.55  fof(f97,plain,(
% 1.44/0.55    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f17])).
% 1.44/0.55  fof(f17,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.44/0.55  fof(f487,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f486,f82])).
% 1.44/0.55  fof(f82,plain,(
% 1.44/0.55    ~v2_struct_0(sK3)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f486,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f485,f148])).
% 1.44/0.55  fof(f148,plain,(
% 1.44/0.55    v2_pre_topc(sK3)),
% 1.44/0.55    inference(subsumption_resolution,[],[f147,f77])).
% 1.44/0.55  fof(f77,plain,(
% 1.44/0.55    v2_pre_topc(sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f147,plain,(
% 1.44/0.55    v2_pre_topc(sK3) | ~v2_pre_topc(sK1)),
% 1.44/0.55    inference(subsumption_resolution,[],[f143,f78])).
% 1.44/0.55  fof(f143,plain,(
% 1.44/0.55    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.44/0.55    inference(resolution,[],[f83,f125])).
% 1.44/0.55  fof(f125,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f45])).
% 1.44/0.55  fof(f45,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f44])).
% 1.44/0.55  fof(f44,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.44/0.55  fof(f485,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f484,f151])).
% 1.44/0.55  fof(f484,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f483,f79])).
% 1.44/0.55  fof(f79,plain,(
% 1.44/0.55    ~v2_struct_0(sK2)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f483,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f482,f80])).
% 1.44/0.55  fof(f80,plain,(
% 1.44/0.55    v2_pre_topc(sK2)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f482,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f481,f81])).
% 1.44/0.55  fof(f81,plain,(
% 1.44/0.55    l1_pre_topc(sK2)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f481,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f480,f86])).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    v1_funct_1(sK5)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f480,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f478,f411])).
% 1.44/0.55  fof(f411,plain,(
% 1.44/0.55    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl11_2),
% 1.44/0.55    inference(backward_demodulation,[],[f87,f410])).
% 1.44/0.55  fof(f410,plain,(
% 1.44/0.55    u1_struct_0(sK3) = u1_struct_0(sK4) | ~spl11_2),
% 1.44/0.55    inference(trivial_inequality_removal,[],[f409])).
% 1.44/0.55  fof(f409,plain,(
% 1.44/0.55    sK4 != sK4 | u1_struct_0(sK3) = u1_struct_0(sK4) | ~spl11_2),
% 1.44/0.55    inference(superposition,[],[f186,f194])).
% 1.44/0.55  fof(f194,plain,(
% 1.44/0.55    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 1.44/0.55    inference(subsumption_resolution,[],[f193,f163])).
% 1.44/0.55  fof(f163,plain,(
% 1.44/0.55    l1_pre_topc(sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f158,f78])).
% 1.44/0.55  fof(f158,plain,(
% 1.44/0.55    l1_pre_topc(sK4) | ~l1_pre_topc(sK1)),
% 1.44/0.55    inference(resolution,[],[f85,f114])).
% 1.44/0.55  fof(f85,plain,(
% 1.44/0.55    m1_pre_topc(sK4,sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f193,plain,(
% 1.44/0.55    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_pre_topc(sK4)),
% 1.44/0.55    inference(resolution,[],[f192,f99])).
% 1.44/0.55  fof(f99,plain,(
% 1.44/0.55    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.44/0.55  fof(f192,plain,(
% 1.44/0.55    v1_pre_topc(sK4)),
% 1.44/0.55    inference(forward_demodulation,[],[f149,f89])).
% 1.44/0.55  fof(f89,plain,(
% 1.44/0.55    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f149,plain,(
% 1.44/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 1.44/0.55    inference(subsumption_resolution,[],[f144,f78])).
% 1.44/0.55  fof(f144,plain,(
% 1.44/0.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK1)),
% 1.44/0.55    inference(resolution,[],[f83,f116])).
% 1.44/0.55  fof(f116,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f14])).
% 1.44/0.55  fof(f14,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.44/0.55  fof(f186,plain,(
% 1.44/0.55    ( ! [X6,X5] : (sK4 != g1_pre_topc(X5,X6) | u1_struct_0(sK3) = X5) ) | ~spl11_2),
% 1.44/0.55    inference(avatar_component_clause,[],[f185])).
% 1.44/0.55  fof(f185,plain,(
% 1.44/0.55    spl11_2 <=> ! [X5,X6] : (sK4 != g1_pre_topc(X5,X6) | u1_struct_0(sK3) = X5)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.44/0.55  fof(f87,plain,(
% 1.44/0.55    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f478,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.44/0.55    inference(resolution,[],[f412,f121])).
% 1.44/0.55  fof(f121,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f39])).
% 1.44/0.55  fof(f39,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f38])).
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f12])).
% 1.44/0.55  fof(f12,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.44/0.55  fof(f412,plain,(
% 1.44/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~spl11_2),
% 1.44/0.55    inference(backward_demodulation,[],[f88,f410])).
% 1.44/0.55  fof(f88,plain,(
% 1.44/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f1018,plain,(
% 1.44/0.55    k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~spl11_2),
% 1.44/0.55    inference(resolution,[],[f841,f364])).
% 1.44/0.55  fof(f364,plain,(
% 1.44/0.55    m1_pre_topc(sK3,sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f363,f151])).
% 1.44/0.55  fof(f363,plain,(
% 1.44/0.55    m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK3)),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f360])).
% 1.44/0.55  fof(f360,plain,(
% 1.44/0.55    m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK3)),
% 1.44/0.55    inference(resolution,[],[f178,f97])).
% 1.44/0.55  fof(f178,plain,(
% 1.44/0.55    ( ! [X1] : (~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK4) | ~l1_pre_topc(X1)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f172,f151])).
% 1.44/0.55  fof(f172,plain,(
% 1.44/0.55    ( ! [X1] : (m1_pre_topc(X1,sK4) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(X1)) )),
% 1.44/0.55    inference(superposition,[],[f112,f89])).
% 1.44/0.55  fof(f112,plain,(
% 1.44/0.55    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f71])).
% 1.44/0.55  fof(f71,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f31])).
% 1.44/0.55  fof(f31,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.44/0.55  fof(f841,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f840,f76])).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    ~v2_struct_0(sK1)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f840,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f839,f77])).
% 1.44/0.55  fof(f839,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f834,f78])).
% 1.44/0.55  fof(f834,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.44/0.55    inference(resolution,[],[f741,f85])).
% 1.44/0.55  fof(f741,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(sK4,X2) | ~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl11_2),
% 1.44/0.55    inference(forward_demodulation,[],[f238,f410])).
% 1.44/0.55  fof(f238,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f237,f126])).
% 1.44/0.55  fof(f126,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f47])).
% 1.44/0.55  fof(f47,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f19])).
% 1.44/0.55  fof(f19,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.44/0.55  fof(f237,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f236,f79])).
% 1.44/0.55  fof(f236,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f235,f80])).
% 1.44/0.55  fof(f235,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f234,f81])).
% 1.44/0.55  fof(f234,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f233,f86])).
% 1.44/0.55  fof(f233,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f224,f87])).
% 1.44/0.55  fof(f224,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.44/0.55    inference(resolution,[],[f88,f120])).
% 1.44/0.55  fof(f120,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f37])).
% 1.44/0.55  fof(f37,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f13])).
% 1.44/0.55  fof(f13,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.44/0.55  fof(f239,plain,(
% 1.44/0.55    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)),
% 1.44/0.55    inference(forward_demodulation,[],[f93,f92])).
% 1.44/0.55  fof(f93,plain,(
% 1.44/0.55    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f740,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,sK5,X1)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f739,f411])).
% 1.44/0.55  fof(f739,plain,(
% 1.44/0.55    ( ! [X1] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(forward_demodulation,[],[f738,f410])).
% 1.44/0.55  fof(f738,plain,(
% 1.44/0.55    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f737,f412])).
% 1.44/0.55  fof(f737,plain,(
% 1.44/0.55    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(forward_demodulation,[],[f736,f410])).
% 1.44/0.55  fof(f736,plain,(
% 1.44/0.55    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f735])).
% 1.44/0.55  fof(f735,plain,(
% 1.44/0.55    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(forward_demodulation,[],[f734,f410])).
% 1.44/0.55  fof(f734,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f733,f79])).
% 1.44/0.55  fof(f733,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f732,f80])).
% 1.44/0.55  fof(f732,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f731,f81])).
% 1.44/0.55  fof(f731,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f730,f84])).
% 1.44/0.55  fof(f84,plain,(
% 1.44/0.55    ~v2_struct_0(sK4)),
% 1.44/0.55    inference(cnf_transformation,[],[f60])).
% 1.44/0.55  fof(f730,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f729,f160])).
% 1.44/0.55  fof(f160,plain,(
% 1.44/0.55    v2_pre_topc(sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f159,f77])).
% 1.44/0.55  fof(f159,plain,(
% 1.44/0.55    v2_pre_topc(sK4) | ~v2_pre_topc(sK1)),
% 1.44/0.55    inference(subsumption_resolution,[],[f155,f78])).
% 1.44/0.55  fof(f155,plain,(
% 1.44/0.55    v2_pre_topc(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.44/0.55    inference(resolution,[],[f85,f125])).
% 1.44/0.55  fof(f729,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f728,f163])).
% 1.44/0.55  fof(f728,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f727,f86])).
% 1.44/0.55  fof(f727,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f726,f82])).
% 1.44/0.55  fof(f726,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_21)),
% 1.44/0.55    inference(subsumption_resolution,[],[f725,f393])).
% 1.44/0.55  fof(f393,plain,(
% 1.44/0.55    v1_tsep_1(sK3,sK4) | ~spl11_21),
% 1.44/0.55    inference(avatar_component_clause,[],[f392])).
% 1.44/0.55  fof(f392,plain,(
% 1.44/0.55    spl11_21 <=> v1_tsep_1(sK3,sK4)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.44/0.55  fof(f725,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~v1_tsep_1(sK3,sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f708,f364])).
% 1.44/0.55  fof(f708,plain,(
% 1.44/0.55    ( ! [X1] : (~r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK3,sK4) | ~v1_tsep_1(sK3,sK4) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.44/0.55    inference(superposition,[],[f132,f662])).
% 1.44/0.55  fof(f662,plain,(
% 1.44/0.55    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK4,sK2,sK5,sK3) | ~spl11_2),
% 1.44/0.55    inference(forward_demodulation,[],[f657,f650])).
% 1.44/0.55  fof(f657,plain,(
% 1.44/0.55    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK3) | ~spl11_2),
% 1.44/0.55    inference(resolution,[],[f632,f364])).
% 1.44/0.55  fof(f632,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))) ) | ~spl11_2),
% 1.44/0.55    inference(forward_demodulation,[],[f232,f410])).
% 1.44/0.55  fof(f232,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f231,f84])).
% 1.44/0.55  fof(f231,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f230,f160])).
% 1.44/0.55  fof(f230,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f229,f163])).
% 1.44/0.55  fof(f229,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f228,f79])).
% 1.44/0.55  fof(f228,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f227,f80])).
% 1.44/0.55  fof(f227,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f226,f81])).
% 1.44/0.55  fof(f226,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f225,f86])).
% 1.44/0.55  fof(f225,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(subsumption_resolution,[],[f223,f87])).
% 1.44/0.55  fof(f223,plain,(
% 1.44/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.44/0.55    inference(resolution,[],[f88,f121])).
% 1.44/0.55  fof(f132,plain,(
% 1.44/0.55    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f123])).
% 1.44/0.55  fof(f123,plain,(
% 1.44/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f73])).
% 1.44/0.55  fof(f73,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f41])).
% 1.44/0.55  fof(f41,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.55    inference(flattening,[],[f40])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).
% 1.44/0.55  fof(f495,plain,(
% 1.44/0.55    ~spl11_2 | spl11_22),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f494])).
% 1.44/0.55  fof(f494,plain,(
% 1.44/0.55    $false | (~spl11_2 | spl11_22)),
% 1.44/0.55    inference(subsumption_resolution,[],[f449,f403])).
% 1.44/0.55  fof(f403,plain,(
% 1.44/0.55    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | spl11_22),
% 1.44/0.55    inference(avatar_component_clause,[],[f402])).
% 1.44/0.55  fof(f402,plain,(
% 1.44/0.55    spl11_22 <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 1.44/0.55  fof(f449,plain,(
% 1.44/0.55    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f448,f163])).
% 1.44/0.55  fof(f448,plain,(
% 1.44/0.55    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~l1_pre_topc(sK4) | ~spl11_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f427,f160])).
% 1.44/0.55  fof(f427,plain,(
% 1.44/0.55    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~spl11_2),
% 1.44/0.55    inference(superposition,[],[f106,f410])).
% 1.44/0.55  fof(f106,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f70])).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f68,f69])).
% 1.44/0.55  fof(f69,plain,(
% 1.44/0.55    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.44/0.55    introduced(choice_axiom,[])).
% 1.44/0.55  fof(f68,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(rectify,[],[f67])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f66])).
% 1.44/0.55  fof(f66,plain,(
% 1.44/0.55    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f52])).
% 1.44/0.55  fof(f52,plain,(
% 1.44/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(definition_folding,[],[f30,f51])).
% 1.44/0.55  fof(f51,plain,(
% 1.44/0.55    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.55  fof(f30,plain,(
% 1.44/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f22])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.44/0.55    inference(rectify,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.44/0.55  fof(f407,plain,(
% 1.44/0.55    spl11_20 | ~spl11_22),
% 1.44/0.55    inference(avatar_split_clause,[],[f406,f402,f388])).
% 1.44/0.55  fof(f388,plain,(
% 1.44/0.55    spl11_20 <=> v3_pre_topc(u1_struct_0(sK3),sK4)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 1.44/0.55  fof(f406,plain,(
% 1.44/0.55    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | v3_pre_topc(u1_struct_0(sK3),sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f383,f163])).
% 1.44/0.55  fof(f383,plain,(
% 1.44/0.55    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | v3_pre_topc(u1_struct_0(sK3),sK4) | ~l1_pre_topc(sK4)),
% 1.44/0.55    inference(resolution,[],[f374,f119])).
% 1.44/0.55  fof(f119,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f72])).
% 1.44/0.55  fof(f72,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.44/0.55  fof(f374,plain,(
% 1.44/0.55    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.44/0.55    inference(subsumption_resolution,[],[f370,f163])).
% 1.44/0.55  fof(f370,plain,(
% 1.44/0.55    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4)),
% 1.44/0.55    inference(resolution,[],[f364,f115])).
% 1.44/0.55  fof(f115,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f33])).
% 1.44/0.55  fof(f33,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f16])).
% 1.44/0.55  fof(f16,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.44/0.55  fof(f399,plain,(
% 1.44/0.55    spl11_21 | ~spl11_20),
% 1.44/0.55    inference(avatar_split_clause,[],[f398,f388,f392])).
% 1.44/0.55  fof(f398,plain,(
% 1.44/0.55    ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK3,sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f397,f160])).
% 1.44/0.55  fof(f397,plain,(
% 1.44/0.55    ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK3,sK4) | ~v2_pre_topc(sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f396,f163])).
% 1.44/0.55  fof(f396,plain,(
% 1.44/0.55    ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK3,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 1.44/0.55    inference(subsumption_resolution,[],[f381,f364])).
% 1.44/0.55  fof(f381,plain,(
% 1.44/0.55    ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK3,sK4) | ~m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)),
% 1.44/0.55    inference(resolution,[],[f374,f135])).
% 1.44/0.55  fof(f135,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f128])).
% 1.44/0.55  fof(f128,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f75])).
% 1.44/0.55  fof(f75,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f74])).
% 1.44/0.55  fof(f74,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.55    inference(nnf_transformation,[],[f49])).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f48])).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f15])).
% 1.44/0.55  fof(f15,axiom,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.44/0.55  fof(f280,plain,(
% 1.44/0.55    spl11_1),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f279])).
% 1.44/0.55  fof(f279,plain,(
% 1.44/0.55    $false | spl11_1),
% 1.44/0.55    inference(subsumption_resolution,[],[f278,f151])).
% 1.44/0.55  fof(f278,plain,(
% 1.44/0.55    ~l1_pre_topc(sK3) | spl11_1),
% 1.44/0.55    inference(resolution,[],[f183,f98])).
% 1.44/0.55  fof(f98,plain,(
% 1.44/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.44/0.55  fof(f183,plain,(
% 1.44/0.55    ~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | spl11_1),
% 1.44/0.55    inference(avatar_component_clause,[],[f181])).
% 1.44/0.55  fof(f181,plain,(
% 1.44/0.55    spl11_1 <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.44/0.55  fof(f187,plain,(
% 1.44/0.55    ~spl11_1 | spl11_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f175,f185,f181])).
% 1.44/0.55  fof(f175,plain,(
% 1.44/0.55    ( ! [X6,X5] : (sK4 != g1_pre_topc(X5,X6) | u1_struct_0(sK3) = X5 | ~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) )),
% 1.44/0.55    inference(superposition,[],[f130,f89])).
% 1.44/0.55  fof(f130,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f50])).
% 1.44/0.55  fof(f50,plain,(
% 1.44/0.55    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.44/0.55    inference(ennf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (31088)------------------------------
% 1.44/0.55  % (31088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (31088)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (31088)Memory used [KB]: 11257
% 1.44/0.55  % (31088)Time elapsed: 0.149 s
% 1.44/0.55  % (31088)------------------------------
% 1.44/0.55  % (31088)------------------------------
% 1.44/0.55  % (31086)Success in time 0.2 s
%------------------------------------------------------------------------------
