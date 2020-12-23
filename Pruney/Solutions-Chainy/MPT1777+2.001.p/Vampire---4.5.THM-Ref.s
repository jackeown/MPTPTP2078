%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:00 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  308 (6964 expanded)
%              Number of leaves         :   37 (3583 expanded)
%              Depth                    :   47
%              Number of atoms          : 1807 (108536 expanded)
%              Number of equality atoms :  121 (14585 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1888,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f364,f372,f376,f517,f616,f630,f954,f1339,f1342,f1887])).

fof(f1887,plain,
    ( ~ spl11_2
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(avatar_contradiction_clause,[],[f1886])).

fof(f1886,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f1885,f103])).

fof(f103,plain,(
    ~ r1_tmap_1(sK4,sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f64,f63,f62,f61,f60,f59,f58])).

fof(f58,plain,
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

fof(f59,plain,
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

fof(f60,plain,
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

fof(f61,plain,
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

fof(f62,plain,
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

fof(f63,plain,
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

fof(f64,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f1885,plain,
    ( r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ spl11_2
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(subsumption_resolution,[],[f1884,f191])).

fof(f191,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f100,f101])).

fof(f101,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f65])).

fof(f1884,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r1_tmap_1(sK4,sK2,sK5,sK6)
    | ~ spl11_2
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(resolution,[],[f1883,f1175])).

fof(f1175,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1174,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f1174,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1173,f89])).

fof(f89,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f1173,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1172,f90])).

fof(f90,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f1172,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1171,f168])).

fof(f168,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f167,f86])).

fof(f86,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f167,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f161,f87])).

fof(f87,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f161,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f92,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f92,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f1171,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1170,f171])).

fof(f171,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f164,f87])).

fof(f164,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f92,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1170,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1169,f95])).

fof(f95,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f65])).

fof(f1169,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1168,f523])).

fof(f523,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f96,f522])).

fof(f522,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl11_2 ),
    inference(trivial_inequality_removal,[],[f521])).

fof(f521,plain,
    ( sK4 != sK4
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl11_2 ),
    inference(superposition,[],[f212,f220])).

fof(f220,plain,(
    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(subsumption_resolution,[],[f219,f186])).

fof(f186,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f179,f87])).

fof(f179,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f94,f121])).

fof(f94,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f219,plain,
    ( sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f218,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f218,plain,(
    v1_pre_topc(sK4) ),
    inference(forward_demodulation,[],[f169,f98])).

fof(f98,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 ),
    inference(cnf_transformation,[],[f65])).

fof(f169,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    inference(subsumption_resolution,[],[f162,f87])).

fof(f162,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f92,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f212,plain,
    ( ! [X6,X7] :
        ( sK4 != g1_pre_topc(X6,X7)
        | u1_struct_0(sK3) = X6 )
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl11_2
  <=> ! [X7,X6] :
        ( sK4 != g1_pre_topc(X6,X7)
        | u1_struct_0(sK3) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f96,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f65])).

fof(f1168,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1167,f524])).

fof(f524,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f97,f522])).

fof(f97,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f1167,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1166,f91])).

fof(f91,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f1166,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f1165,f643])).

fof(f643,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f642,f168])).

fof(f642,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f641,f171])).

fof(f641,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f640,f462])).

fof(f462,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(resolution,[],[f459,f202])).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f194,f171])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f127,f98])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f459,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(subsumption_resolution,[],[f458,f171])).

fof(f458,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(duplicate_literal_removal,[],[f455])).

fof(f455,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f203,f104])).

fof(f104,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f203,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK3)
      | m1_pre_topc(X2,sK4)
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f196,f171])).

fof(f196,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK4)
      | ~ m1_pre_topc(X2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f119,f98])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f640,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f636,f618])).

fof(f618,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ spl11_2
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f355,f522])).

fof(f355,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl11_16
  <=> v3_pre_topc(u1_struct_0(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f636,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f532,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f532,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f332,f522])).

fof(f332,plain,(
    m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f326,f171])).

fof(f326,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f320,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f320,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(subsumption_resolution,[],[f318,f186])).

fof(f318,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f202,f104])).

fof(f1165,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ v1_tsep_1(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1164,f462])).

fof(f1164,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1163,f191])).

fof(f1163,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(duplicate_literal_removal,[],[f1162])).

fof(f1162,plain,
    ( r1_tmap_1(sK3,sK2,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK3)
    | ~ v1_tsep_1(sK3,sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl11_2 ),
    inference(resolution,[],[f1161,f147])).

fof(f147,plain,(
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
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f1161,plain,
    ( r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),sK6)
    | ~ spl11_2 ),
    inference(backward_demodulation,[],[f278,f1160])).

fof(f1160,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK3,sK2,sK5,sK3)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f1155,f850])).

fof(f850,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f845,f171])).

fof(f845,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f606,f104])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f605,f91])).

fof(f605,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f604,f168])).

fof(f604,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f603,f171])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f602,f88])).

fof(f602,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f601,f89])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f600,f90])).

fof(f600,plain,
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
    inference(subsumption_resolution,[],[f599,f95])).

fof(f599,plain,
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
    inference(subsumption_resolution,[],[f596,f523])).

fof(f596,plain,
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
    inference(resolution,[],[f524,f129])).

fof(f129,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f1155,plain,
    ( k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3))
    | ~ spl11_2 ),
    inference(resolution,[],[f963,f459])).

fof(f963,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f962,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f962,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f961,f86])).

fof(f961,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f956,f87])).

fof(f956,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | ~ spl11_2 ),
    inference(resolution,[],[f879,f94])).

fof(f879,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(sK4,X2)
        | ~ m1_pre_topc(X1,sK4)
        | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X1))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f266,f522])).

fof(f266,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f265,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f265,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f264,f88])).

fof(f264,plain,(
    ! [X2,X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(sK4,X2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f263,f89])).

fof(f263,plain,(
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
    inference(subsumption_resolution,[],[f262,f90])).

fof(f262,plain,(
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
    inference(subsumption_resolution,[],[f261,f95])).

fof(f261,plain,(
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
    inference(subsumption_resolution,[],[f251,f96])).

fof(f251,plain,(
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
    inference(resolution,[],[f97,f128])).

fof(f128,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f278,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6) ),
    inference(forward_demodulation,[],[f102,f101])).

fof(f102,plain,(
    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) ),
    inference(cnf_transformation,[],[f65])).

fof(f1883,plain,
    ( ! [X0] :
        ( ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK4,sK2,sK5,X0) )
    | ~ spl11_2
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(duplicate_literal_removal,[],[f1882])).

fof(f1882,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | r1_tmap_1(sK4,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_2
    | ~ spl11_17
    | ~ spl11_41 ),
    inference(resolution,[],[f1023,f953])).

fof(f953,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f952])).

fof(f952,plain,
    ( spl11_41
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f1023,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK3,sK2,sK5,X0) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(duplicate_literal_removal,[],[f1022])).

fof(f1022,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(forward_demodulation,[],[f1021,f522])).

fof(f1021,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1020,f88])).

fof(f1020,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1019,f89])).

fof(f1019,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1018,f90])).

fof(f1018,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1017,f91])).

fof(f1017,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1016,f168])).

fof(f1016,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1015,f171])).

fof(f1015,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1014,f95])).

fof(f1014,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1013,f523])).

fof(f1013,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1012,f524])).

fof(f1012,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1011,f93])).

fof(f93,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f1011,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v2_struct_0(sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f1010,f358])).

fof(f358,plain,
    ( v1_tsep_1(sK4,sK3)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl11_17
  <=> v1_tsep_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f1010,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ v1_tsep_1(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1008,f320])).

fof(f1008,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0)
        | ~ r1_tmap_1(sK3,sK2,sK5,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_pre_topc(sK4,sK3)
        | ~ v1_tsep_1(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(superposition,[],[f148,f973])).

fof(f973,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK3,sK2,sK5,sK4)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f852,f850])).

fof(f852,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK5,sK4)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f849,f522])).

fof(f849,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4))
    | ~ spl11_2 ),
    inference(resolution,[],[f606,f320])).

fof(f148,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
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
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
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
    inference(cnf_transformation,[],[f78])).

fof(f1342,plain,(
    spl11_39 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | spl11_39 ),
    inference(subsumption_resolution,[],[f934,f1203])).

fof(f1203,plain,(
    m1_pre_topc(sK4,sK4) ),
    inference(subsumption_resolution,[],[f1193,f459])).

fof(f1193,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ m1_pre_topc(sK3,sK4) ),
    inference(superposition,[],[f1176,f98])).

fof(f1176,plain,(
    ! [X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4)
      | ~ m1_pre_topc(X1,sK4) ) ),
    inference(subsumption_resolution,[],[f760,f776])).

fof(f776,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK4)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) ) ),
    inference(subsumption_resolution,[],[f766,f171])).

fof(f766,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK4)
      | l1_pre_topc(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f321,f121])).

fof(f321,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
      | ~ m1_pre_topc(X0,sK4) ) ),
    inference(subsumption_resolution,[],[f319,f186])).

fof(f319,plain,(
    ! [X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3)
      | ~ m1_pre_topc(X0,sK4)
      | ~ l1_pre_topc(sK4) ) ),
    inference(resolution,[],[f202,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f760,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK4)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ),
    inference(resolution,[],[f321,f203])).

fof(f934,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | spl11_39 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl11_39
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).

fof(f1339,plain,
    ( ~ spl11_2
    | ~ spl11_30
    | spl11_38 ),
    inference(avatar_contradiction_clause,[],[f1338])).

fof(f1338,plain,
    ( $false
    | ~ spl11_2
    | ~ spl11_30
    | spl11_38 ),
    inference(subsumption_resolution,[],[f1337,f1203])).

fof(f1337,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ spl11_2
    | ~ spl11_30
    | spl11_38 ),
    inference(subsumption_resolution,[],[f1336,f930])).

fof(f930,plain,
    ( ~ v1_tsep_1(sK4,sK4)
    | spl11_38 ),
    inference(avatar_component_clause,[],[f928])).

fof(f928,plain,
    ( spl11_38
  <=> v1_tsep_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f1336,plain,
    ( v1_tsep_1(sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ spl11_2
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f1335,f500])).

fof(f500,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl11_30
  <=> v3_pre_topc(u1_struct_0(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f1335,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f1333,f532])).

fof(f1333,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(u1_struct_0(sK3),sK4)
    | v1_tsep_1(sK4,sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ spl11_2 ),
    inference(superposition,[],[f592,f522])).

fof(f592,plain,
    ( ! [X29] :
        ( ~ m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(X29),sK4)
        | v1_tsep_1(X29,sK4)
        | ~ m1_pre_topc(X29,sK4) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f591,f183])).

fof(f183,plain,(
    v2_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f182,f86])).

fof(f182,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f176,f87])).

fof(f176,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f94,f133])).

fof(f591,plain,
    ( ! [X29] :
        ( ~ m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(X29),sK4)
        | v1_tsep_1(X29,sK4)
        | ~ m1_pre_topc(X29,sK4)
        | ~ v2_pre_topc(sK4) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f564,f186])).

fof(f564,plain,
    ( ! [X29] :
        ( ~ m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(u1_struct_0(X29),sK4)
        | v1_tsep_1(X29,sK4)
        | ~ m1_pre_topc(X29,sK4)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4) )
    | ~ spl11_2 ),
    inference(superposition,[],[f150,f522])).

fof(f954,plain,
    ( ~ spl11_38
    | ~ spl11_39
    | spl11_41
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f950,f211,f952,f932,f928])).

fof(f950,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f949,f523])).

fof(f949,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f948,f522])).

fof(f948,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f947,f524])).

fof(f947,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f946,f522])).

fof(f946,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f945,f522])).

fof(f945,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f944,f88])).

fof(f944,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f943,f89])).

fof(f943,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f942,f90])).

fof(f942,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f941,f183])).

fof(f941,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f940,f186])).

fof(f940,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f939,f95])).

fof(f939,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f913,f93])).

fof(f913,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | v2_struct_0(sK4)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK4)
        | ~ v2_pre_topc(sK4)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl11_2 ),
    inference(duplicate_literal_removal,[],[f912])).

fof(f912,plain,
    ( ! [X1] :
        ( ~ r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1)
        | r1_tmap_1(sK4,sK2,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_pre_topc(sK4,sK4)
        | ~ v1_tsep_1(sK4,sK4)
        | v2_struct_0(sK4)
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
    inference(superposition,[],[f147,f891])).

fof(f891,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK4,sK2,sK5,sK4)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f862,f850])).

fof(f862,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK4)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f861,f522])).

fof(f861,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK2,sK5,sK4)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f858,f186])).

fof(f858,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK2,sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl11_2 ),
    inference(resolution,[],[f839,f104])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f260,f522])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f259,f93])).

fof(f259,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f258,f183])).

fof(f258,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f257,f186])).

fof(f257,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f256,f88])).

fof(f256,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f255,f89])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f254,f90])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK4)
      | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f253,f95])).

fof(f253,plain,(
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
    inference(subsumption_resolution,[],[f250,f96])).

fof(f250,plain,(
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
    inference(resolution,[],[f97,f129])).

fof(f630,plain,
    ( ~ spl11_2
    | spl11_32 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl11_2
    | spl11_32 ),
    inference(subsumption_resolution,[],[f571,f513])).

fof(f513,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | spl11_32 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl11_32
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f571,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f570,f186])).

fof(f570,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f546,f183])).

fof(f546,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl11_2 ),
    inference(superposition,[],[f113,f522])).

fof(f113,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f73,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r1_tarski(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
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
    inference(rectify,[],[f72])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f32,f56])).

fof(f56,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f616,plain,
    ( ~ spl11_2
    | spl11_18 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl11_2
    | spl11_18 ),
    inference(subsumption_resolution,[],[f614,f171])).

fof(f614,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl11_2
    | spl11_18 ),
    inference(subsumption_resolution,[],[f613,f168])).

fof(f613,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl11_2
    | spl11_18 ),
    inference(resolution,[],[f536,f113])).

fof(f536,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl11_2
    | spl11_18 ),
    inference(backward_demodulation,[],[f368,f522])).

fof(f368,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl11_18
  <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f517,plain,
    ( spl11_30
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f516,f512,f498])).

fof(f516,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | v3_pre_topc(u1_struct_0(sK3),sK4) ),
    inference(subsumption_resolution,[],[f492,f186])).

fof(f492,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | v3_pre_topc(u1_struct_0(sK3),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f474,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f474,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subsumption_resolution,[],[f467,f186])).

fof(f467,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f459,f122])).

fof(f376,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f373,f171])).

fof(f373,plain,
    ( ~ l1_pre_topc(sK3)
    | spl11_1 ),
    inference(resolution,[],[f209,f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f209,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl11_1
  <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f372,plain,
    ( spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f371,f367,f353])).

fof(f371,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | v3_pre_topc(u1_struct_0(sK4),sK3) ),
    inference(subsumption_resolution,[],[f347,f171])).

fof(f347,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | v3_pre_topc(u1_struct_0(sK4),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f332,f126])).

fof(f364,plain,
    ( spl11_17
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f363,f353,f357])).

fof(f363,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | v1_tsep_1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f362,f168])).

fof(f362,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f361,f171])).

fof(f361,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f345,f320])).

fof(f345,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK4),sK3)
    | v1_tsep_1(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f332,f150])).

fof(f213,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f199,f211,f207])).

fof(f199,plain,(
    ! [X6,X7] :
      ( sK4 != g1_pre_topc(X6,X7)
      | u1_struct_0(sK3) = X6
      | ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ) ),
    inference(superposition,[],[f140,f98])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (16757)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (16751)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (16750)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (16754)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (16759)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (16767)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (16770)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (16748)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (16747)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.21/0.52  % (16762)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.21/0.52  % (16752)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.21/0.53  % (16769)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.21/0.53  % (16766)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.21/0.53  % (16761)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.21/0.53  % (16764)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.21/0.53  % (16772)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.21/0.53  % (16753)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.21/0.53  % (16749)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.37/0.54  % (16760)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.37/0.54  % (16758)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.37/0.54  % (16756)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.37/0.54  % (16754)Refutation not found, incomplete strategy% (16754)------------------------------
% 1.37/0.54  % (16754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (16768)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.37/0.54  % (16771)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.37/0.55  % (16763)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.37/0.55  % (16747)Refutation not found, incomplete strategy% (16747)------------------------------
% 1.37/0.55  % (16747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16747)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16747)Memory used [KB]: 10874
% 1.37/0.55  % (16747)Time elapsed: 0.131 s
% 1.37/0.55  % (16747)------------------------------
% 1.37/0.55  % (16747)------------------------------
% 1.37/0.55  % (16755)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.37/0.55  % (16752)Refutation not found, incomplete strategy% (16752)------------------------------
% 1.37/0.55  % (16752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16754)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16754)Memory used [KB]: 2046
% 1.37/0.55  % (16754)Time elapsed: 0.109 s
% 1.37/0.55  % (16754)------------------------------
% 1.37/0.55  % (16754)------------------------------
% 1.37/0.56  % (16752)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (16752)Memory used [KB]: 6652
% 1.37/0.56  % (16752)Time elapsed: 0.141 s
% 1.37/0.56  % (16752)------------------------------
% 1.37/0.56  % (16752)------------------------------
% 1.37/0.57  % (16765)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.37/0.58  % (16748)Refutation found. Thanks to Tanya!
% 1.37/0.58  % SZS status Theorem for theBenchmark
% 1.37/0.58  % SZS output start Proof for theBenchmark
% 1.37/0.58  fof(f1888,plain,(
% 1.37/0.58    $false),
% 1.37/0.58    inference(avatar_sat_refutation,[],[f213,f364,f372,f376,f517,f616,f630,f954,f1339,f1342,f1887])).
% 1.37/0.58  fof(f1887,plain,(
% 1.37/0.58    ~spl11_2 | ~spl11_16 | ~spl11_17 | ~spl11_41),
% 1.37/0.58    inference(avatar_contradiction_clause,[],[f1886])).
% 1.37/0.58  fof(f1886,plain,(
% 1.37/0.58    $false | (~spl11_2 | ~spl11_16 | ~spl11_17 | ~spl11_41)),
% 1.37/0.58    inference(subsumption_resolution,[],[f1885,f103])).
% 1.37/0.58  fof(f103,plain,(
% 1.37/0.58    ~r1_tmap_1(sK4,sK2,sK5,sK6)),
% 1.37/0.58    inference(cnf_transformation,[],[f65])).
% 1.37/0.58  fof(f65,plain,(
% 1.37/0.58    ((((((~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.37/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f26,f64,f63,f62,f61,f60,f59,f58])).
% 1.37/0.58  fof(f58,plain,(
% 1.37/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f59,plain,(
% 1.37/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK1,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f60,plain,(
% 1.37/0.58    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(X2,sK2,k3_tmap_1(sK1,sK2,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f61,plain,(
% 1.37/0.58    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,X3,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f62,plain,(
% 1.37/0.58    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,X4,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4 & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK5))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f63,plain,(
% 1.37/0.58    ? [X5] : (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,X5) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,u1_struct_0(sK4))) => (? [X6] : (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f64,plain,(
% 1.37/0.58    ? [X6] : (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),X6) & sK6 = X6 & m1_subset_1(X6,u1_struct_0(sK3))) => (~r1_tmap_1(sK4,sK2,sK5,sK6) & r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3)))),
% 1.37/0.58    introduced(choice_axiom,[])).
% 1.37/0.58  fof(f26,plain,(
% 1.37/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.37/0.58    inference(flattening,[],[f25])).
% 1.37/0.58  fof(f25,plain,(
% 1.37/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f23])).
% 1.37/0.60  fof(f23,negated_conjecture,(
% 1.37/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.37/0.60    inference(negated_conjecture,[],[f22])).
% 1.37/0.60  fof(f22,conjecture,(
% 1.37/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.37/0.60  fof(f1885,plain,(
% 1.37/0.60    r1_tmap_1(sK4,sK2,sK5,sK6) | (~spl11_2 | ~spl11_16 | ~spl11_17 | ~spl11_41)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1884,f191])).
% 1.37/0.60  fof(f191,plain,(
% 1.37/0.60    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.37/0.60    inference(forward_demodulation,[],[f100,f101])).
% 1.37/0.60  fof(f101,plain,(
% 1.37/0.60    sK6 = sK7),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f100,plain,(
% 1.37/0.60    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1884,plain,(
% 1.37/0.60    ~m1_subset_1(sK6,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,sK5,sK6) | (~spl11_2 | ~spl11_16 | ~spl11_17 | ~spl11_41)),
% 1.37/0.60    inference(resolution,[],[f1883,f1175])).
% 1.37/0.60  fof(f1175,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1174,f88])).
% 1.37/0.60  fof(f88,plain,(
% 1.37/0.60    ~v2_struct_0(sK2)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1174,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1173,f89])).
% 1.37/0.60  fof(f89,plain,(
% 1.37/0.60    v2_pre_topc(sK2)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1173,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1172,f90])).
% 1.37/0.60  fof(f90,plain,(
% 1.37/0.60    l1_pre_topc(sK2)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1172,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1171,f168])).
% 1.37/0.60  fof(f168,plain,(
% 1.37/0.60    v2_pre_topc(sK3)),
% 1.37/0.60    inference(subsumption_resolution,[],[f167,f86])).
% 1.37/0.60  fof(f86,plain,(
% 1.37/0.60    v2_pre_topc(sK1)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f167,plain,(
% 1.37/0.60    v2_pre_topc(sK3) | ~v2_pre_topc(sK1)),
% 1.37/0.60    inference(subsumption_resolution,[],[f161,f87])).
% 1.37/0.60  fof(f87,plain,(
% 1.37/0.60    l1_pre_topc(sK1)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f161,plain,(
% 1.37/0.60    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.37/0.60    inference(resolution,[],[f92,f133])).
% 1.37/0.60  fof(f133,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f48])).
% 1.37/0.60  fof(f48,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.60    inference(flattening,[],[f47])).
% 1.37/0.60  fof(f47,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.60    inference(ennf_transformation,[],[f4])).
% 1.37/0.60  fof(f4,axiom,(
% 1.37/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.37/0.60  fof(f92,plain,(
% 1.37/0.60    m1_pre_topc(sK3,sK1)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1171,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1170,f171])).
% 1.37/0.60  fof(f171,plain,(
% 1.37/0.60    l1_pre_topc(sK3)),
% 1.37/0.60    inference(subsumption_resolution,[],[f164,f87])).
% 1.37/0.60  fof(f164,plain,(
% 1.37/0.60    l1_pre_topc(sK3) | ~l1_pre_topc(sK1)),
% 1.37/0.60    inference(resolution,[],[f92,f121])).
% 1.37/0.60  fof(f121,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f34])).
% 1.37/0.60  fof(f34,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f7])).
% 1.37/0.60  fof(f7,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.37/0.60  fof(f1170,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1169,f95])).
% 1.37/0.60  fof(f95,plain,(
% 1.37/0.60    v1_funct_1(sK5)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1169,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1168,f523])).
% 1.37/0.60  fof(f523,plain,(
% 1.37/0.60    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl11_2),
% 1.37/0.60    inference(backward_demodulation,[],[f96,f522])).
% 1.37/0.60  fof(f522,plain,(
% 1.37/0.60    u1_struct_0(sK3) = u1_struct_0(sK4) | ~spl11_2),
% 1.37/0.60    inference(trivial_inequality_removal,[],[f521])).
% 1.37/0.60  fof(f521,plain,(
% 1.37/0.60    sK4 != sK4 | u1_struct_0(sK3) = u1_struct_0(sK4) | ~spl11_2),
% 1.37/0.60    inference(superposition,[],[f212,f220])).
% 1.37/0.60  fof(f220,plain,(
% 1.37/0.60    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 1.37/0.60    inference(subsumption_resolution,[],[f219,f186])).
% 1.37/0.60  fof(f186,plain,(
% 1.37/0.60    l1_pre_topc(sK4)),
% 1.37/0.60    inference(subsumption_resolution,[],[f179,f87])).
% 1.37/0.60  fof(f179,plain,(
% 1.37/0.60    l1_pre_topc(sK4) | ~l1_pre_topc(sK1)),
% 1.37/0.60    inference(resolution,[],[f94,f121])).
% 1.37/0.60  fof(f94,plain,(
% 1.37/0.60    m1_pre_topc(sK4,sK1)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f219,plain,(
% 1.37/0.60    sK4 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_pre_topc(sK4)),
% 1.37/0.60    inference(resolution,[],[f218,f106])).
% 1.37/0.60  fof(f106,plain,(
% 1.37/0.60    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f30])).
% 1.37/0.60  fof(f30,plain,(
% 1.37/0.60    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(flattening,[],[f29])).
% 1.37/0.60  fof(f29,plain,(
% 1.37/0.60    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f3])).
% 1.37/0.60  fof(f3,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.37/0.60  fof(f218,plain,(
% 1.37/0.60    v1_pre_topc(sK4)),
% 1.37/0.60    inference(forward_demodulation,[],[f169,f98])).
% 1.37/0.60  fof(f98,plain,(
% 1.37/0.60    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = sK4),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f169,plain,(
% 1.37/0.60    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 1.37/0.60    inference(subsumption_resolution,[],[f162,f87])).
% 1.37/0.60  fof(f162,plain,(
% 1.37/0.60    v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~l1_pre_topc(sK1)),
% 1.37/0.60    inference(resolution,[],[f92,f123])).
% 1.37/0.60  fof(f123,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f36])).
% 1.37/0.60  fof(f36,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f15])).
% 1.37/0.60  fof(f15,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.37/0.60  fof(f212,plain,(
% 1.37/0.60    ( ! [X6,X7] : (sK4 != g1_pre_topc(X6,X7) | u1_struct_0(sK3) = X6) ) | ~spl11_2),
% 1.37/0.60    inference(avatar_component_clause,[],[f211])).
% 1.37/0.60  fof(f211,plain,(
% 1.37/0.60    spl11_2 <=> ! [X7,X6] : (sK4 != g1_pre_topc(X6,X7) | u1_struct_0(sK3) = X6)),
% 1.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.37/0.60  fof(f96,plain,(
% 1.37/0.60    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1168,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1167,f524])).
% 1.37/0.60  fof(f524,plain,(
% 1.37/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~spl11_2),
% 1.37/0.60    inference(backward_demodulation,[],[f97,f522])).
% 1.37/0.60  fof(f97,plain,(
% 1.37/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1167,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1166,f91])).
% 1.37/0.60  fof(f91,plain,(
% 1.37/0.60    ~v2_struct_0(sK3)),
% 1.37/0.60    inference(cnf_transformation,[],[f65])).
% 1.37/0.60  fof(f1166,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f1165,f643])).
% 1.37/0.60  fof(f643,plain,(
% 1.37/0.60    v1_tsep_1(sK3,sK3) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f642,f168])).
% 1.37/0.60  fof(f642,plain,(
% 1.37/0.60    v1_tsep_1(sK3,sK3) | ~v2_pre_topc(sK3) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f641,f171])).
% 1.37/0.60  fof(f641,plain,(
% 1.37/0.60    v1_tsep_1(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f640,f462])).
% 1.37/0.60  fof(f462,plain,(
% 1.37/0.60    m1_pre_topc(sK3,sK3)),
% 1.37/0.60    inference(resolution,[],[f459,f202])).
% 1.37/0.60  fof(f202,plain,(
% 1.37/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK4) | m1_pre_topc(X0,sK3)) )),
% 1.37/0.60    inference(subsumption_resolution,[],[f194,f171])).
% 1.37/0.60  fof(f194,plain,(
% 1.37/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK4) | m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) )),
% 1.37/0.60    inference(superposition,[],[f127,f98])).
% 1.37/0.60  fof(f127,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f38])).
% 1.37/0.60  fof(f38,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f11])).
% 1.37/0.60  fof(f11,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 1.37/0.60  fof(f459,plain,(
% 1.37/0.60    m1_pre_topc(sK3,sK4)),
% 1.37/0.60    inference(subsumption_resolution,[],[f458,f171])).
% 1.37/0.60  fof(f458,plain,(
% 1.37/0.60    m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK3)),
% 1.37/0.60    inference(duplicate_literal_removal,[],[f455])).
% 1.37/0.60  fof(f455,plain,(
% 1.37/0.60    m1_pre_topc(sK3,sK4) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK3)),
% 1.37/0.60    inference(resolution,[],[f203,f104])).
% 1.37/0.60  fof(f104,plain,(
% 1.37/0.60    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f27])).
% 1.37/0.60  fof(f27,plain,(
% 1.37/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f18])).
% 1.37/0.60  fof(f18,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.37/0.60  fof(f203,plain,(
% 1.37/0.60    ( ! [X2] : (~m1_pre_topc(X2,sK3) | m1_pre_topc(X2,sK4) | ~l1_pre_topc(X2)) )),
% 1.37/0.60    inference(subsumption_resolution,[],[f196,f171])).
% 1.37/0.60  fof(f196,plain,(
% 1.37/0.60    ( ! [X2] : (m1_pre_topc(X2,sK4) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(X2)) )),
% 1.37/0.60    inference(superposition,[],[f119,f98])).
% 1.37/0.60  fof(f119,plain,(
% 1.37/0.60    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f76])).
% 1.37/0.60  fof(f76,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(nnf_transformation,[],[f33])).
% 1.37/0.60  fof(f33,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f12])).
% 1.37/0.60  fof(f12,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.37/0.60  fof(f640,plain,(
% 1.37/0.60    v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(subsumption_resolution,[],[f636,f618])).
% 1.37/0.60  fof(f618,plain,(
% 1.37/0.60    v3_pre_topc(u1_struct_0(sK3),sK3) | (~spl11_2 | ~spl11_16)),
% 1.37/0.60    inference(forward_demodulation,[],[f355,f522])).
% 1.37/0.60  fof(f355,plain,(
% 1.37/0.60    v3_pre_topc(u1_struct_0(sK4),sK3) | ~spl11_16),
% 1.37/0.60    inference(avatar_component_clause,[],[f353])).
% 1.37/0.60  fof(f353,plain,(
% 1.37/0.60    spl11_16 <=> v3_pre_topc(u1_struct_0(sK4),sK3)),
% 1.37/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 1.37/0.60  fof(f636,plain,(
% 1.37/0.60    ~v3_pre_topc(u1_struct_0(sK3),sK3) | v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~spl11_2),
% 1.37/0.60    inference(resolution,[],[f532,f150])).
% 1.37/0.60  fof(f150,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.60    inference(equality_resolution,[],[f138])).
% 1.37/0.60  fof(f138,plain,(
% 1.37/0.60    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f81])).
% 1.37/0.60  fof(f81,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.60    inference(flattening,[],[f80])).
% 1.37/0.60  fof(f80,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.60    inference(nnf_transformation,[],[f54])).
% 1.37/0.60  fof(f54,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.60    inference(flattening,[],[f53])).
% 1.37/0.60  fof(f53,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.60    inference(ennf_transformation,[],[f16])).
% 1.37/0.60  fof(f16,axiom,(
% 1.37/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.37/0.60  fof(f532,plain,(
% 1.37/0.60    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl11_2),
% 1.37/0.60    inference(backward_demodulation,[],[f332,f522])).
% 1.37/0.60  fof(f332,plain,(
% 1.37/0.60    m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.37/0.60    inference(subsumption_resolution,[],[f326,f171])).
% 1.37/0.60  fof(f326,plain,(
% 1.37/0.60    m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3)),
% 1.37/0.60    inference(resolution,[],[f320,f122])).
% 1.37/0.60  fof(f122,plain,(
% 1.37/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f35])).
% 1.37/0.60  fof(f35,plain,(
% 1.37/0.60    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.37/0.60    inference(ennf_transformation,[],[f17])).
% 1.37/0.60  fof(f17,axiom,(
% 1.37/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.37/0.60  fof(f320,plain,(
% 1.37/0.60    m1_pre_topc(sK4,sK3)),
% 1.37/0.60    inference(subsumption_resolution,[],[f318,f186])).
% 1.37/0.60  fof(f318,plain,(
% 1.37/0.60    m1_pre_topc(sK4,sK3) | ~l1_pre_topc(sK4)),
% 1.37/0.60    inference(resolution,[],[f202,f104])).
% 1.37/0.60  fof(f1165,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~v1_tsep_1(sK3,sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl11_2),
% 1.37/0.60    inference(subsumption_resolution,[],[f1164,f462])).
% 1.37/0.60  fof(f1164,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~m1_pre_topc(sK3,sK3) | ~v1_tsep_1(sK3,sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl11_2),
% 1.37/0.60    inference(subsumption_resolution,[],[f1163,f191])).
% 1.37/0.60  fof(f1163,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK3) | ~v1_tsep_1(sK3,sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl11_2),
% 1.37/0.60    inference(duplicate_literal_removal,[],[f1162])).
% 1.37/0.60  fof(f1162,plain,(
% 1.37/0.60    r1_tmap_1(sK3,sK2,sK5,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK3) | ~v1_tsep_1(sK3,sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl11_2),
% 1.37/0.60    inference(resolution,[],[f1161,f147])).
% 1.37/0.60  fof(f147,plain,(
% 1.37/0.60    ( ! [X2,X0,X5,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.60    inference(equality_resolution,[],[f131])).
% 1.37/0.60  fof(f131,plain,(
% 1.37/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.60    inference(cnf_transformation,[],[f78])).
% 1.37/0.61  fof(f78,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.61    inference(nnf_transformation,[],[f44])).
% 1.37/0.61  fof(f44,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.61    inference(flattening,[],[f43])).
% 1.37/0.61  fof(f43,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f20])).
% 1.37/0.61  fof(f20,axiom,(
% 1.37/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 1.37/0.61  fof(f1161,plain,(
% 1.37/0.61    r1_tmap_1(sK3,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),sK6) | ~spl11_2),
% 1.37/0.61    inference(backward_demodulation,[],[f278,f1160])).
% 1.37/0.61  fof(f1160,plain,(
% 1.37/0.61    k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_tmap_1(sK3,sK2,sK5,sK3) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f1155,f850])).
% 1.37/0.61  fof(f850,plain,(
% 1.37/0.61    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f845,f171])).
% 1.37/0.61  fof(f845,plain,(
% 1.37/0.61    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f606,f104])).
% 1.37/0.61  fof(f606,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f605,f91])).
% 1.37/0.61  fof(f605,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f604,f168])).
% 1.37/0.61  fof(f604,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f603,f171])).
% 1.37/0.61  fof(f603,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f602,f88])).
% 1.37/0.61  fof(f602,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f601,f89])).
% 1.37/0.61  fof(f601,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f600,f90])).
% 1.37/0.61  fof(f600,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f599,f95])).
% 1.37/0.61  fof(f599,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f596,f523])).
% 1.37/0.61  fof(f596,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_tmap_1(sK3,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f524,f129])).
% 1.37/0.61  fof(f129,plain,(
% 1.37/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f42])).
% 1.37/0.61  fof(f42,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.61    inference(flattening,[],[f41])).
% 1.37/0.61  fof(f41,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f13])).
% 1.37/0.61  fof(f13,axiom,(
% 1.37/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.37/0.61  fof(f1155,plain,(
% 1.37/0.61    k3_tmap_1(sK1,sK2,sK4,sK3,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f963,f459])).
% 1.37/0.61  fof(f963,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f962,f85])).
% 1.37/0.61  fof(f85,plain,(
% 1.37/0.61    ~v2_struct_0(sK1)),
% 1.37/0.61    inference(cnf_transformation,[],[f65])).
% 1.37/0.61  fof(f962,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f961,f86])).
% 1.37/0.61  fof(f961,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f956,f87])).
% 1.37/0.61  fof(f956,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0)) = k3_tmap_1(sK1,sK2,sK4,X0,sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) ) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f879,f94])).
% 1.37/0.61  fof(f879,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(sK4,X2) | ~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f266,f522])).
% 1.37/0.61  fof(f266,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f265,f134])).
% 1.37/0.61  fof(f134,plain,(
% 1.37/0.61    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f50])).
% 1.37/0.61  fof(f50,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.61    inference(flattening,[],[f49])).
% 1.37/0.61  fof(f49,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f21])).
% 1.37/0.61  fof(f21,axiom,(
% 1.37/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.37/0.61  fof(f265,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f264,f88])).
% 1.37/0.61  fof(f264,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f263,f89])).
% 1.37/0.61  fof(f263,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f262,f90])).
% 1.37/0.61  fof(f262,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f261,f95])).
% 1.37/0.61  fof(f261,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f251,f96])).
% 1.37/0.61  fof(f251,plain,(
% 1.37/0.61    ( ! [X2,X1] : (~m1_pre_topc(X1,sK4) | k3_tmap_1(X2,sK2,sK4,X1,sK5) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X1)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(sK4,X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.37/0.61    inference(resolution,[],[f97,f128])).
% 1.37/0.61  fof(f128,plain,(
% 1.37/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f40])).
% 1.37/0.61  fof(f40,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.61    inference(flattening,[],[f39])).
% 1.37/0.61  fof(f39,plain,(
% 1.37/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.61    inference(ennf_transformation,[],[f14])).
% 1.37/0.61  fof(f14,axiom,(
% 1.37/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.37/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.37/0.61  fof(f278,plain,(
% 1.37/0.61    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK6)),
% 1.37/0.61    inference(forward_demodulation,[],[f102,f101])).
% 1.37/0.61  fof(f102,plain,(
% 1.37/0.61    r1_tmap_1(sK3,sK2,k3_tmap_1(sK1,sK2,sK4,sK3,sK5),sK7)),
% 1.37/0.61    inference(cnf_transformation,[],[f65])).
% 1.37/0.61  fof(f1883,plain,(
% 1.37/0.61    ( ! [X0] : (~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,sK5,X0)) ) | (~spl11_2 | ~spl11_17 | ~spl11_41)),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f1882])).
% 1.37/0.61  fof(f1882,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,sK5,X0) | r1_tmap_1(sK4,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl11_2 | ~spl11_17 | ~spl11_41)),
% 1.37/0.61    inference(resolution,[],[f1023,f953])).
% 1.37/0.61  fof(f953,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | ~spl11_41),
% 1.37/0.61    inference(avatar_component_clause,[],[f952])).
% 1.37/0.61  fof(f952,plain,(
% 1.37/0.61    spl11_41 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,sK5,X1) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 1.37/0.61  fof(f1023,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r1_tmap_1(sK3,sK2,sK5,X0)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f1022])).
% 1.37/0.61  fof(f1022,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(forward_demodulation,[],[f1021,f522])).
% 1.37/0.61  fof(f1021,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1020,f88])).
% 1.37/0.61  fof(f1020,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1019,f89])).
% 1.37/0.61  fof(f1019,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1018,f90])).
% 1.37/0.61  fof(f1018,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1017,f91])).
% 1.37/0.61  fof(f1017,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1016,f168])).
% 1.37/0.61  fof(f1016,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1015,f171])).
% 1.37/0.61  fof(f1015,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1014,f95])).
% 1.37/0.61  fof(f1014,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1013,f523])).
% 1.37/0.61  fof(f1013,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1012,f524])).
% 1.37/0.61  fof(f1012,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1011,f93])).
% 1.37/0.61  fof(f93,plain,(
% 1.37/0.61    ~v2_struct_0(sK4)),
% 1.37/0.61    inference(cnf_transformation,[],[f65])).
% 1.37/0.61  fof(f1011,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl11_2 | ~spl11_17)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1010,f358])).
% 1.37/0.61  fof(f358,plain,(
% 1.37/0.61    v1_tsep_1(sK4,sK3) | ~spl11_17),
% 1.37/0.61    inference(avatar_component_clause,[],[f357])).
% 1.37/0.61  fof(f357,plain,(
% 1.37/0.61    spl11_17 <=> v1_tsep_1(sK4,sK3)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.37/0.61  fof(f1010,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~v1_tsep_1(sK4,sK3) | v2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f1008,f320])).
% 1.37/0.61  fof(f1008,plain,(
% 1.37/0.61    ( ! [X0] : (r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X0) | ~r1_tmap_1(sK3,sK2,sK5,X0) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(sK4,sK3) | ~v1_tsep_1(sK4,sK3) | v2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(superposition,[],[f148,f973])).
% 1.37/0.61  fof(f973,plain,(
% 1.37/0.61    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK3,sK2,sK5,sK4) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f852,f850])).
% 1.37/0.61  fof(f852,plain,(
% 1.37/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK3,sK2,sK5,sK4) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f849,f522])).
% 1.37/0.61  fof(f849,plain,(
% 1.37/0.61    k2_tmap_1(sK3,sK2,sK5,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f606,f320])).
% 1.37/0.61  fof(f148,plain,(
% 1.37/0.61    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.61    inference(equality_resolution,[],[f130])).
% 1.37/0.61  fof(f130,plain,(
% 1.37/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f78])).
% 1.37/0.61  fof(f1342,plain,(
% 1.37/0.61    spl11_39),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f1341])).
% 1.37/0.61  fof(f1341,plain,(
% 1.37/0.61    $false | spl11_39),
% 1.37/0.61    inference(subsumption_resolution,[],[f934,f1203])).
% 1.37/0.61  fof(f1203,plain,(
% 1.37/0.61    m1_pre_topc(sK4,sK4)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1193,f459])).
% 1.37/0.61  fof(f1193,plain,(
% 1.37/0.61    m1_pre_topc(sK4,sK4) | ~m1_pre_topc(sK3,sK4)),
% 1.37/0.61    inference(superposition,[],[f1176,f98])).
% 1.37/0.61  fof(f1176,plain,(
% 1.37/0.61    ( ! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4) | ~m1_pre_topc(X1,sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f760,f776])).
% 1.37/0.61  fof(f776,plain,(
% 1.37/0.61    ( ! [X9] : (~m1_pre_topc(X9,sK4) | l1_pre_topc(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f766,f171])).
% 1.37/0.61  fof(f766,plain,(
% 1.37/0.61    ( ! [X9] : (~m1_pre_topc(X9,sK4) | l1_pre_topc(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | ~l1_pre_topc(sK3)) )),
% 1.37/0.61    inference(resolution,[],[f321,f121])).
% 1.37/0.61  fof(f321,plain,(
% 1.37/0.61    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) | ~m1_pre_topc(X0,sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f319,f186])).
% 1.37/0.61  fof(f319,plain,(
% 1.37/0.61    ( ! [X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK3) | ~m1_pre_topc(X0,sK4) | ~l1_pre_topc(sK4)) )),
% 1.37/0.61    inference(resolution,[],[f202,f124])).
% 1.37/0.61  fof(f124,plain,(
% 1.37/0.61    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f36])).
% 1.37/0.61  fof(f760,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_pre_topc(X1,sK4) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),sK4) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) )),
% 1.37/0.61    inference(resolution,[],[f321,f203])).
% 1.37/0.61  fof(f934,plain,(
% 1.37/0.61    ~m1_pre_topc(sK4,sK4) | spl11_39),
% 1.37/0.61    inference(avatar_component_clause,[],[f932])).
% 1.37/0.61  fof(f932,plain,(
% 1.37/0.61    spl11_39 <=> m1_pre_topc(sK4,sK4)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_39])])).
% 1.37/0.61  fof(f1339,plain,(
% 1.37/0.61    ~spl11_2 | ~spl11_30 | spl11_38),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f1338])).
% 1.37/0.61  fof(f1338,plain,(
% 1.37/0.61    $false | (~spl11_2 | ~spl11_30 | spl11_38)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1337,f1203])).
% 1.37/0.61  fof(f1337,plain,(
% 1.37/0.61    ~m1_pre_topc(sK4,sK4) | (~spl11_2 | ~spl11_30 | spl11_38)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1336,f930])).
% 1.37/0.61  fof(f930,plain,(
% 1.37/0.61    ~v1_tsep_1(sK4,sK4) | spl11_38),
% 1.37/0.61    inference(avatar_component_clause,[],[f928])).
% 1.37/0.61  fof(f928,plain,(
% 1.37/0.61    spl11_38 <=> v1_tsep_1(sK4,sK4)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 1.37/0.61  fof(f1336,plain,(
% 1.37/0.61    v1_tsep_1(sK4,sK4) | ~m1_pre_topc(sK4,sK4) | (~spl11_2 | ~spl11_30)),
% 1.37/0.61    inference(subsumption_resolution,[],[f1335,f500])).
% 1.37/0.61  fof(f500,plain,(
% 1.37/0.61    v3_pre_topc(u1_struct_0(sK3),sK4) | ~spl11_30),
% 1.37/0.61    inference(avatar_component_clause,[],[f498])).
% 1.37/0.61  fof(f498,plain,(
% 1.37/0.61    spl11_30 <=> v3_pre_topc(u1_struct_0(sK3),sK4)),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 1.37/0.61  fof(f1335,plain,(
% 1.37/0.61    ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK4,sK4) | ~m1_pre_topc(sK4,sK4) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f1333,f532])).
% 1.37/0.61  fof(f1333,plain,(
% 1.37/0.61    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(sK3),sK4) | v1_tsep_1(sK4,sK4) | ~m1_pre_topc(sK4,sK4) | ~spl11_2),
% 1.37/0.61    inference(superposition,[],[f592,f522])).
% 1.37/0.61  fof(f592,plain,(
% 1.37/0.61    ( ! [X29] : (~m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X29),sK4) | v1_tsep_1(X29,sK4) | ~m1_pre_topc(X29,sK4)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f591,f183])).
% 1.37/0.61  fof(f183,plain,(
% 1.37/0.61    v2_pre_topc(sK4)),
% 1.37/0.61    inference(subsumption_resolution,[],[f182,f86])).
% 1.37/0.61  fof(f182,plain,(
% 1.37/0.61    v2_pre_topc(sK4) | ~v2_pre_topc(sK1)),
% 1.37/0.61    inference(subsumption_resolution,[],[f176,f87])).
% 1.37/0.61  fof(f176,plain,(
% 1.37/0.61    v2_pre_topc(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.37/0.61    inference(resolution,[],[f94,f133])).
% 1.37/0.61  fof(f591,plain,(
% 1.37/0.61    ( ! [X29] : (~m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X29),sK4) | v1_tsep_1(X29,sK4) | ~m1_pre_topc(X29,sK4) | ~v2_pre_topc(sK4)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f564,f186])).
% 1.37/0.61  fof(f564,plain,(
% 1.37/0.61    ( ! [X29] : (~m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X29),sK4) | v1_tsep_1(X29,sK4) | ~m1_pre_topc(X29,sK4) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4)) ) | ~spl11_2),
% 1.37/0.61    inference(superposition,[],[f150,f522])).
% 1.37/0.61  fof(f954,plain,(
% 1.37/0.61    ~spl11_38 | ~spl11_39 | spl11_41 | ~spl11_2),
% 1.37/0.61    inference(avatar_split_clause,[],[f950,f211,f952,f932,f928])).
% 1.37/0.61  fof(f950,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f949,f523])).
% 1.37/0.61  fof(f949,plain,(
% 1.37/0.61    ( ! [X1] : (~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4)) ) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f948,f522])).
% 1.37/0.61  fof(f948,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f947,f524])).
% 1.37/0.61  fof(f947,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f946,f522])).
% 1.37/0.61  fof(f946,plain,(
% 1.37/0.61    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f945,f522])).
% 1.37/0.61  fof(f945,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2))) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f944,f88])).
% 1.37/0.61  fof(f944,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f943,f89])).
% 1.37/0.61  fof(f943,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f942,f90])).
% 1.37/0.61  fof(f942,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f941,f183])).
% 1.37/0.61  fof(f941,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f940,f186])).
% 1.37/0.61  fof(f940,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f939,f95])).
% 1.37/0.61  fof(f939,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f913,f93])).
% 1.37/0.61  fof(f913,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(duplicate_literal_removal,[],[f912])).
% 1.37/0.61  fof(f912,plain,(
% 1.37/0.61    ( ! [X1] : (~r1_tmap_1(sK4,sK2,k2_tmap_1(sK3,sK2,sK5,sK3),X1) | r1_tmap_1(sK4,sK2,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK4) | ~v1_tsep_1(sK4,sK4) | v2_struct_0(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl11_2),
% 1.37/0.61    inference(superposition,[],[f147,f891])).
% 1.37/0.61  fof(f891,plain,(
% 1.37/0.61    k2_tmap_1(sK3,sK2,sK5,sK3) = k2_tmap_1(sK4,sK2,sK5,sK4) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f862,f850])).
% 1.37/0.61  fof(f862,plain,(
% 1.37/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK4,sK2,sK5,sK4) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f861,f522])).
% 1.37/0.61  fof(f861,plain,(
% 1.37/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK2,sK5,sK4) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f858,f186])).
% 1.37/0.61  fof(f858,plain,(
% 1.37/0.61    k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK4,sK2,sK5,sK4) | ~l1_pre_topc(sK4) | ~spl11_2),
% 1.37/0.61    inference(resolution,[],[f839,f104])).
% 1.37/0.61  fof(f839,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(X0))) ) | ~spl11_2),
% 1.37/0.61    inference(forward_demodulation,[],[f260,f522])).
% 1.37/0.61  fof(f260,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0))) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f259,f93])).
% 1.37/0.61  fof(f259,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f258,f183])).
% 1.37/0.61  fof(f258,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f257,f186])).
% 1.37/0.61  fof(f257,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f256,f88])).
% 1.37/0.61  fof(f256,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f255,f89])).
% 1.37/0.61  fof(f255,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f254,f90])).
% 1.37/0.61  fof(f254,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f253,f95])).
% 1.37/0.61  fof(f253,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(subsumption_resolution,[],[f250,f96])).
% 1.37/0.61  fof(f250,plain,(
% 1.37/0.61    ( ! [X0] : (~m1_pre_topc(X0,sK4) | k2_tmap_1(sK4,sK2,sK5,X0) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK2),sK5,u1_struct_0(X0)) | ~v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK2)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4)) )),
% 1.37/0.61    inference(resolution,[],[f97,f129])).
% 1.37/0.61  fof(f630,plain,(
% 1.37/0.61    ~spl11_2 | spl11_32),
% 1.37/0.61    inference(avatar_contradiction_clause,[],[f629])).
% 1.37/0.61  fof(f629,plain,(
% 1.37/0.61    $false | (~spl11_2 | spl11_32)),
% 1.37/0.61    inference(subsumption_resolution,[],[f571,f513])).
% 1.37/0.61  fof(f513,plain,(
% 1.37/0.61    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | spl11_32),
% 1.37/0.61    inference(avatar_component_clause,[],[f512])).
% 1.37/0.61  fof(f512,plain,(
% 1.37/0.61    spl11_32 <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 1.37/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 1.37/0.61  fof(f571,plain,(
% 1.37/0.61    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f570,f186])).
% 1.37/0.61  fof(f570,plain,(
% 1.37/0.61    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~l1_pre_topc(sK4) | ~spl11_2),
% 1.37/0.61    inference(subsumption_resolution,[],[f546,f183])).
% 1.37/0.61  fof(f546,plain,(
% 1.37/0.61    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~v2_pre_topc(sK4) | ~l1_pre_topc(sK4) | ~spl11_2),
% 1.37/0.61    inference(superposition,[],[f113,f522])).
% 1.37/0.61  fof(f113,plain,(
% 1.37/0.61    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.61    inference(cnf_transformation,[],[f75])).
% 1.37/0.61  fof(f75,plain,(
% 1.37/0.61    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f73,f74])).
% 1.37/0.61  fof(f74,plain,(
% 1.37/0.61    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.37/0.61    introduced(choice_axiom,[])).
% 1.37/0.61  fof(f73,plain,(
% 1.37/0.61    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(rectify,[],[f72])).
% 1.37/0.61  fof(f72,plain,(
% 1.37/0.61    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(flattening,[],[f71])).
% 1.37/0.61  fof(f71,plain,(
% 1.37/0.61    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(nnf_transformation,[],[f57])).
% 1.37/0.61  fof(f57,plain,(
% 1.37/0.61    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.61    inference(definition_folding,[],[f32,f56])).
% 1.37/0.61  fof(f56,plain,(
% 1.37/0.61    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.37/0.62  fof(f32,plain,(
% 1.37/0.62    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(flattening,[],[f31])).
% 1.37/0.62  fof(f31,plain,(
% 1.37/0.62    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(ennf_transformation,[],[f24])).
% 1.37/0.62  fof(f24,plain,(
% 1.37/0.62    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.37/0.62    inference(rectify,[],[f5])).
% 1.37/0.62  fof(f5,axiom,(
% 1.37/0.62    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.37/0.62  fof(f616,plain,(
% 1.37/0.62    ~spl11_2 | spl11_18),
% 1.37/0.62    inference(avatar_contradiction_clause,[],[f615])).
% 1.37/0.62  fof(f615,plain,(
% 1.37/0.62    $false | (~spl11_2 | spl11_18)),
% 1.37/0.62    inference(subsumption_resolution,[],[f614,f171])).
% 1.37/0.62  fof(f614,plain,(
% 1.37/0.62    ~l1_pre_topc(sK3) | (~spl11_2 | spl11_18)),
% 1.37/0.62    inference(subsumption_resolution,[],[f613,f168])).
% 1.37/0.62  fof(f613,plain,(
% 1.37/0.62    ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | (~spl11_2 | spl11_18)),
% 1.37/0.62    inference(resolution,[],[f536,f113])).
% 1.37/0.62  fof(f536,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | (~spl11_2 | spl11_18)),
% 1.37/0.62    inference(backward_demodulation,[],[f368,f522])).
% 1.37/0.62  fof(f368,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) | spl11_18),
% 1.37/0.62    inference(avatar_component_clause,[],[f367])).
% 1.37/0.62  fof(f367,plain,(
% 1.37/0.62    spl11_18 <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))),
% 1.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.37/0.62  fof(f517,plain,(
% 1.37/0.62    spl11_30 | ~spl11_32),
% 1.37/0.62    inference(avatar_split_clause,[],[f516,f512,f498])).
% 1.37/0.62  fof(f516,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | v3_pre_topc(u1_struct_0(sK3),sK4)),
% 1.37/0.62    inference(subsumption_resolution,[],[f492,f186])).
% 1.37/0.62  fof(f492,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | v3_pre_topc(u1_struct_0(sK3),sK4) | ~l1_pre_topc(sK4)),
% 1.37/0.62    inference(resolution,[],[f474,f126])).
% 1.37/0.62  fof(f126,plain,(
% 1.37/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f77])).
% 1.37/0.62  fof(f77,plain,(
% 1.37/0.62    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(nnf_transformation,[],[f37])).
% 1.37/0.62  fof(f37,plain,(
% 1.37/0.62    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(ennf_transformation,[],[f6])).
% 1.37/0.62  fof(f6,axiom,(
% 1.37/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.37/0.62  fof(f474,plain,(
% 1.37/0.62    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.37/0.62    inference(subsumption_resolution,[],[f467,f186])).
% 1.37/0.62  fof(f467,plain,(
% 1.37/0.62    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_pre_topc(sK4)),
% 1.37/0.62    inference(resolution,[],[f459,f122])).
% 1.37/0.62  fof(f376,plain,(
% 1.37/0.62    spl11_1),
% 1.37/0.62    inference(avatar_contradiction_clause,[],[f375])).
% 1.37/0.62  fof(f375,plain,(
% 1.37/0.62    $false | spl11_1),
% 1.37/0.62    inference(subsumption_resolution,[],[f373,f171])).
% 1.37/0.62  fof(f373,plain,(
% 1.37/0.62    ~l1_pre_topc(sK3) | spl11_1),
% 1.37/0.62    inference(resolution,[],[f209,f105])).
% 1.37/0.62  fof(f105,plain,(
% 1.37/0.62    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.37/0.62    inference(cnf_transformation,[],[f28])).
% 1.37/0.62  fof(f28,plain,(
% 1.37/0.62    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.62    inference(ennf_transformation,[],[f8])).
% 1.37/0.62  fof(f8,axiom,(
% 1.37/0.62    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.37/0.62  fof(f209,plain,(
% 1.37/0.62    ~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | spl11_1),
% 1.37/0.62    inference(avatar_component_clause,[],[f207])).
% 1.37/0.62  fof(f207,plain,(
% 1.37/0.62    spl11_1 <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 1.37/0.62    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.37/0.62  fof(f372,plain,(
% 1.37/0.62    spl11_16 | ~spl11_18),
% 1.37/0.62    inference(avatar_split_clause,[],[f371,f367,f353])).
% 1.37/0.62  fof(f371,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) | v3_pre_topc(u1_struct_0(sK4),sK3)),
% 1.37/0.62    inference(subsumption_resolution,[],[f347,f171])).
% 1.37/0.62  fof(f347,plain,(
% 1.37/0.62    ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) | v3_pre_topc(u1_struct_0(sK4),sK3) | ~l1_pre_topc(sK3)),
% 1.37/0.62    inference(resolution,[],[f332,f126])).
% 1.37/0.62  fof(f364,plain,(
% 1.37/0.62    spl11_17 | ~spl11_16),
% 1.37/0.62    inference(avatar_split_clause,[],[f363,f353,f357])).
% 1.37/0.62  fof(f363,plain,(
% 1.37/0.62    ~v3_pre_topc(u1_struct_0(sK4),sK3) | v1_tsep_1(sK4,sK3)),
% 1.37/0.62    inference(subsumption_resolution,[],[f362,f168])).
% 1.37/0.62  fof(f362,plain,(
% 1.37/0.62    ~v3_pre_topc(u1_struct_0(sK4),sK3) | v1_tsep_1(sK4,sK3) | ~v2_pre_topc(sK3)),
% 1.37/0.62    inference(subsumption_resolution,[],[f361,f171])).
% 1.37/0.62  fof(f361,plain,(
% 1.37/0.62    ~v3_pre_topc(u1_struct_0(sK4),sK3) | v1_tsep_1(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.37/0.62    inference(subsumption_resolution,[],[f345,f320])).
% 1.37/0.62  fof(f345,plain,(
% 1.37/0.62    ~v3_pre_topc(u1_struct_0(sK4),sK3) | v1_tsep_1(sK4,sK3) | ~m1_pre_topc(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 1.37/0.62    inference(resolution,[],[f332,f150])).
% 1.37/0.62  fof(f213,plain,(
% 1.37/0.62    ~spl11_1 | spl11_2),
% 1.37/0.62    inference(avatar_split_clause,[],[f199,f211,f207])).
% 1.37/0.62  fof(f199,plain,(
% 1.37/0.62    ( ! [X6,X7] : (sK4 != g1_pre_topc(X6,X7) | u1_struct_0(sK3) = X6 | ~m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) )),
% 1.37/0.62    inference(superposition,[],[f140,f98])).
% 1.37/0.62  fof(f140,plain,(
% 1.37/0.62    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.37/0.62    inference(cnf_transformation,[],[f55])).
% 1.37/0.62  fof(f55,plain,(
% 1.37/0.62    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.62    inference(ennf_transformation,[],[f9])).
% 1.37/0.62  fof(f9,axiom,(
% 1.37/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.37/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.37/0.62  % SZS output end Proof for theBenchmark
% 1.37/0.62  % (16748)------------------------------
% 1.37/0.62  % (16748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.62  % (16748)Termination reason: Refutation
% 1.37/0.62  
% 1.37/0.62  % (16748)Memory used [KB]: 11513
% 1.37/0.62  % (16748)Time elapsed: 0.164 s
% 1.37/0.62  % (16748)------------------------------
% 1.37/0.62  % (16748)------------------------------
% 1.37/0.62  % (16744)Success in time 0.251 s
%------------------------------------------------------------------------------
