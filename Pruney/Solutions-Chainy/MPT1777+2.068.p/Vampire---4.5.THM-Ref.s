%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:13 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  171 (4126 expanded)
%              Number of leaves         :   21 (2124 expanded)
%              Depth                    :   25
%              Number of atoms          : 1112 (62618 expanded)
%              Number of equality atoms :   82 (8402 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1069,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1068,f103])).

fof(f103,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f69,f68])).

fof(f68,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f44,f43,f42,f41,f40,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f69,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f1068,plain,(
    ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(forward_demodulation,[],[f1063,f947])).

fof(f947,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(backward_demodulation,[],[f942,f946])).

fof(f946,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK2,sK1,sK3,sK2,sK4) ),
    inference(backward_demodulation,[],[f941,f945])).

fof(f945,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f923,f187])).

fof(f187,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f151,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f151,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f140,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f140,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f54,f59,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f923,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f52,f53,f54,f228,f61,f747])).

fof(f747,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(sK3,X7)
      | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ m1_pre_topc(X6,sK3)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f746,f198])).

fof(f198,plain,(
    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f148,f192])).

fof(f192,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f172,f71])).

fof(f172,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f167,f72])).

fof(f167,plain,(
    l1_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f54,f61,f76])).

fof(f148,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f63,f144])).

fof(f144,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f117,f71])).

fof(f117,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f57,f72])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f746,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f745,f197])).

fof(f197,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f149,f192])).

fof(f149,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f64,f144])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f745,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X6,sK3)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6))
      | ~ m1_pre_topc(sK3,X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(superposition,[],[f456,f192])).

fof(f456,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X3,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f455,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f455,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X3,X5)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f454,f56])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f454,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X3,X5)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f448,f57])).

fof(f448,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | ~ m1_pre_topc(X4,X3)
      | ~ v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1))
      | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4))
      | ~ m1_pre_topc(X3,X5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5) ) ),
    inference(superposition,[],[f134,f144])).

fof(f134,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
      | ~ m1_pre_topc(X10,X11)
      | ~ v1_funct_2(sK4,u1_struct_0(X11),u1_struct_0(X12))
      | k3_tmap_1(X13,X12,X11,X10,sK4) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK4,u1_struct_0(X10))
      | ~ m1_pre_topc(X11,X13)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13) ) ),
    inference(subsumption_resolution,[],[f131,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f131,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_pre_topc(X10,X11)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
      | ~ v1_funct_2(sK4,u1_struct_0(X11),u1_struct_0(X12))
      | k3_tmap_1(X13,X12,X11,X10,sK4) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK4,u1_struct_0(X10))
      | ~ m1_pre_topc(X10,X13)
      | ~ m1_pre_topc(X11,X13)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13) ) ),
    inference(resolution,[],[f62,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f62,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f228,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(forward_demodulation,[],[f227,f190])).

fof(f190,plain,(
    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f65,f187])).

fof(f65,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f227,plain,(
    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(forward_demodulation,[],[f219,f187])).

fof(f219,plain,(
    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(unit_resulting_resolution,[],[f140,f140,f152,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f152,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f140,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f941,plain,(
    k3_tmap_1(sK2,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f925,f187])).

fof(f925,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK3,sK2,sK4) ),
    inference(unit_resulting_resolution,[],[f58,f142,f140,f228,f517,f747])).

fof(f517,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f167,f173,f163])).

fof(f163,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f156,f65])).

fof(f156,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f140,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f173,plain,(
    m1_pre_topc(sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f167,f73])).

fof(f142,plain,(
    v2_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f53,f54,f59,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f58,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f942,plain,(
    k3_tmap_1(sK2,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(backward_demodulation,[],[f939,f941])).

fof(f939,plain,(
    k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f927,f187])).

fof(f927,plain,(
    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4) ),
    inference(unit_resulting_resolution,[],[f60,f169,f167,f228,f173,f747])).

fof(f169,plain,(
    v2_pre_topc(sK3) ),
    inference(unit_resulting_resolution,[],[f53,f54,f61,f82])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f1063,plain,(
    ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5) ),
    inference(unit_resulting_resolution,[],[f60,f169,f167,f173,f798,f1054])).

fof(f1054,plain,(
    ! [X2] :
      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5)
      | ~ v1_tsep_1(sK2,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1053,f58])).

fof(f1053,plain,(
    ! [X2] :
      ( ~ v1_tsep_1(sK2,X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1052,f228])).

fof(f1052,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(sK2,sK3)
      | ~ v1_tsep_1(sK2,X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1048,f191])).

fof(f191,plain,(
    m1_subset_1(sK5,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f104,f187])).

fof(f104,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f67,f68])).

fof(f67,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1048,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK5,k2_struct_0(sK2))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ v1_tsep_1(sK2,X2)
      | ~ r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5)
      | ~ m1_pre_topc(sK3,X2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f1009,f187])).

fof(f1009,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ v1_tsep_1(X0,X1)
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1008,f70])).

fof(f70,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK3)
      | ~ v1_tsep_1(X0,X1)
      | ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
      | r1_tmap_1(sK3,sK1,sK4,sK5)
      | ~ m1_pre_topc(sK3,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f859,f199])).

fof(f199,plain,(
    m1_subset_1(sK5,k2_struct_0(sK3)) ),
    inference(backward_demodulation,[],[f66,f192])).

fof(f66,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f859,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,k2_struct_0(sK3))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_pre_topc(X10,sK3)
      | ~ v1_tsep_1(X10,X11)
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9)
      | r1_tmap_1(sK3,sK1,sK4,X9)
      | ~ m1_pre_topc(sK3,X11)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f858,f60])).

fof(f858,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X9,k2_struct_0(sK3))
      | ~ m1_pre_topc(X10,sK3)
      | ~ v1_tsep_1(X10,X11)
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9)
      | r1_tmap_1(sK3,sK1,sK4,X9)
      | ~ m1_pre_topc(sK3,X11)
      | v2_struct_0(sK3)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f857,f198])).

fof(f857,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X9,k2_struct_0(sK3))
      | ~ m1_pre_topc(X10,sK3)
      | ~ v1_tsep_1(X10,X11)
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,X9)
      | ~ m1_pre_topc(sK3,X11)
      | v2_struct_0(sK3)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f853,f197])).

fof(f853,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ m1_subset_1(X9,k2_struct_0(sK3))
      | ~ m1_pre_topc(X10,sK3)
      | ~ v1_tsep_1(X10,X11)
      | ~ r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9)
      | ~ v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))
      | r1_tmap_1(sK3,sK1,sK4,X9)
      | ~ m1_pre_topc(sK3,X11)
      | v2_struct_0(sK3)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X11)
      | ~ v2_pre_topc(X11)
      | v2_struct_0(X11) ) ),
    inference(superposition,[],[f510,f192])).

fof(f510,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_pre_topc(X6,X4)
      | ~ v1_tsep_1(X6,X7)
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | r1_tmap_1(X4,sK1,sK4,X5)
      | ~ m1_pre_topc(X4,X7)
      | v2_struct_0(X4)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f509,f55])).

fof(f509,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_pre_topc(X6,X4)
      | ~ v1_tsep_1(X6,X7)
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | r1_tmap_1(X4,sK1,sK4,X5)
      | ~ m1_pre_topc(X4,X7)
      | v2_struct_0(X4)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f508,f56])).

fof(f508,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_pre_topc(X6,X4)
      | ~ v1_tsep_1(X6,X7)
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | r1_tmap_1(X4,sK1,sK4,X5)
      | ~ m1_pre_topc(X4,X7)
      | v2_struct_0(X4)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f498,f57])).

fof(f498,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1))))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_pre_topc(X6,X4)
      | ~ v1_tsep_1(X6,X7)
      | ~ r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5)
      | ~ v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1))
      | r1_tmap_1(X4,sK1,sK4,X5)
      | ~ m1_pre_topc(X4,X7)
      | v2_struct_0(X4)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f133,f144])).

fof(f133,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_pre_topc(X5,X8)
      | ~ v1_tsep_1(X5,X7)
      | ~ r1_tmap_1(X5,X6,k3_tmap_1(X7,X6,X8,X5,sK4),X9)
      | ~ v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6))
      | r1_tmap_1(X8,X6,sK4,X9)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(X8)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f130,f83])).

fof(f130,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r1_tmap_1(X5,X6,k3_tmap_1(X7,X6,X8,X5,sK4),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_pre_topc(X5,X8)
      | ~ m1_pre_topc(X5,X7)
      | ~ v1_tsep_1(X5,X7)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
      | ~ v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6))
      | r1_tmap_1(X8,X6,sK4,X9)
      | ~ m1_pre_topc(X8,X7)
      | v2_struct_0(X8)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f62,f100])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | r1_tmap_1(X3,X0,X4,X6)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
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
      ( r1_tmap_1(X3,X0,X4,X5)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X0,X4,X5)
                                  | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f798,plain,(
    v1_tsep_1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f169,f167,f173,f695,f373])).

fof(f373,plain,(
    ! [X5] :
      ( ~ v1_tsep_1(sK3,X5)
      | ~ m1_pre_topc(sK3,X5)
      | v1_tsep_1(sK2,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f372,f190])).

fof(f372,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(sK3,X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(forward_demodulation,[],[f371,f190])).

fof(f371,plain,(
    ! [X5] :
      ( ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f370,f76])).

fof(f370,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f369,f82])).

fof(f369,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f368,f142])).

fof(f368,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f352,f140])).

fof(f352,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | ~ v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5)
      | v1_tsep_1(sK2,X5)
      | ~ v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(superposition,[],[f97,f187])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f695,plain,(
    v1_tsep_1(sK3,sK3) ),
    inference(subsumption_resolution,[],[f694,f173])).

fof(f694,plain,
    ( v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3) ),
    inference(subsumption_resolution,[],[f692,f183])).

fof(f183,plain,(
    v3_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(subsumption_resolution,[],[f179,f169])).

fof(f179,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f167,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f692,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | v1_tsep_1(sK3,sK3)
    | ~ m1_pre_topc(sK3,sK3) ),
    inference(superposition,[],[f405,f192])).

fof(f405,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(u1_struct_0(X2),sK3)
      | v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f404,f402])).

fof(f402,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f392,f167])).

fof(f392,plain,(
    ! [X0] :
      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(superposition,[],[f77,f192])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f404,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(u1_struct_0(X2),sK3)
      | v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3) ) ),
    inference(subsumption_resolution,[],[f403,f169])).

fof(f403,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(u1_struct_0(X2),sK3)
      | v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ v2_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f394,f167])).

fof(f394,plain,(
    ! [X2] :
      ( ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3)))
      | ~ v3_pre_topc(u1_struct_0(X2),sK3)
      | v1_tsep_1(X2,sK3)
      | ~ m1_pre_topc(X2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3) ) ),
    inference(superposition,[],[f94,f192])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
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
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:47:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (5388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (5382)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (5373)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (5386)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (5390)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (5375)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (5381)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (5373)Refutation not found, incomplete strategy% (5373)------------------------------
% 0.21/0.50  % (5373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5378)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5389)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (5387)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5376)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5377)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (5380)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (5393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (5379)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (5373)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5373)Memory used [KB]: 6652
% 0.21/0.51  % (5373)Time elapsed: 0.075 s
% 0.21/0.51  % (5373)------------------------------
% 0.21/0.51  % (5373)------------------------------
% 0.21/0.51  % (5392)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (5391)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (5383)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (5384)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (5385)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5374)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.52  % (5388)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f1069,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(subsumption_resolution,[],[f1068,f103])).
% 1.27/0.53  fof(f103,plain,(
% 1.27/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.27/0.53    inference(backward_demodulation,[],[f69,f68])).
% 1.27/0.53  fof(f68,plain,(
% 1.27/0.53    sK5 = sK6),
% 1.27/0.53    inference(cnf_transformation,[],[f45])).
% 1.27/0.53  fof(f45,plain,(
% 1.27/0.53    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f44,f43,f42,f41,f40,f39,f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 1.27/0.54    introduced(choice_axiom,[])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/0.54    inference(flattening,[],[f16])).
% 1.27/0.54  fof(f16,plain,(
% 1.27/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f15])).
% 1.27/0.54  fof(f15,negated_conjecture,(
% 1.27/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.27/0.54    inference(negated_conjecture,[],[f14])).
% 1.27/0.54  fof(f14,conjecture,(
% 1.27/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f1068,plain,(
% 1.27/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 1.27/0.54    inference(forward_demodulation,[],[f1063,f947])).
% 1.27/0.54  fof(f947,plain,(
% 1.27/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.27/0.54    inference(backward_demodulation,[],[f942,f946])).
% 1.27/0.54  fof(f946,plain,(
% 1.27/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k3_tmap_1(sK2,sK1,sK3,sK2,sK4)),
% 1.27/0.54    inference(backward_demodulation,[],[f941,f945])).
% 1.27/0.54  fof(f945,plain,(
% 1.27/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 1.27/0.54    inference(forward_demodulation,[],[f923,f187])).
% 1.27/0.54  fof(f187,plain,(
% 1.27/0.54    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f151,f71])).
% 1.27/0.54  fof(f71,plain,(
% 1.27/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.27/0.54  fof(f151,plain,(
% 1.27/0.54    l1_struct_0(sK2)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f140,f72])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.27/0.54  fof(f140,plain,(
% 1.27/0.54    l1_pre_topc(sK2)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f54,f59,f76])).
% 1.27/0.54  fof(f76,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    m1_pre_topc(sK2,sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f54,plain,(
% 1.27/0.54    l1_pre_topc(sK0)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f923,plain,(
% 1.27/0.54    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2))),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f52,f53,f54,f228,f61,f747])).
% 1.27/0.54  fof(f747,plain,(
% 1.27/0.54    ( ! [X6,X7] : (~m1_pre_topc(sK3,X7) | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6)) | ~m1_pre_topc(X6,sK3) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f746,f198])).
% 1.27/0.54  fof(f198,plain,(
% 1.27/0.54    v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1))),
% 1.27/0.54    inference(backward_demodulation,[],[f148,f192])).
% 1.27/0.54  fof(f192,plain,(
% 1.27/0.54    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f172,f71])).
% 1.27/0.54  fof(f172,plain,(
% 1.27/0.54    l1_struct_0(sK3)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f167,f72])).
% 1.27/0.54  fof(f167,plain,(
% 1.27/0.54    l1_pre_topc(sK3)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f54,f61,f76])).
% 1.27/0.54  fof(f148,plain,(
% 1.27/0.54    v1_funct_2(sK4,u1_struct_0(sK3),k2_struct_0(sK1))),
% 1.27/0.54    inference(backward_demodulation,[],[f63,f144])).
% 1.27/0.54  fof(f144,plain,(
% 1.27/0.54    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f117,f71])).
% 1.27/0.54  fof(f117,plain,(
% 1.27/0.54    l1_struct_0(sK1)),
% 1.27/0.54    inference(unit_resulting_resolution,[],[f57,f72])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    l1_pre_topc(sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f63,plain,(
% 1.27/0.54    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f746,plain,(
% 1.27/0.54    ( ! [X6,X7] : (~m1_pre_topc(X6,sK3) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6)) | ~m1_pre_topc(sK3,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f745,f197])).
% 1.27/0.54  fof(f197,plain,(
% 1.27/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1))))),
% 1.27/0.54    inference(backward_demodulation,[],[f149,f192])).
% 1.27/0.54  fof(f149,plain,(
% 1.27/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),k2_struct_0(sK1))))),
% 1.27/0.54    inference(backward_demodulation,[],[f64,f144])).
% 1.27/0.54  fof(f64,plain,(
% 1.27/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f745,plain,(
% 1.27/0.54    ( ! [X6,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_pre_topc(X6,sK3) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | k3_tmap_1(X7,sK1,sK3,X6,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(X6)) | ~m1_pre_topc(sK3,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.27/0.54    inference(superposition,[],[f456,f192])).
% 1.27/0.54  fof(f456,plain,(
% 1.27/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X4,X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X3,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f455,f55])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ~v2_struct_0(sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f455,plain,(
% 1.27/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X4,X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X3,X5) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f454,f56])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    v2_pre_topc(sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f45])).
% 1.27/0.54  fof(f454,plain,(
% 1.27/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X4,X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X3,X5) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f448,f57])).
% 1.27/0.54  fof(f448,plain,(
% 1.27/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | ~m1_pre_topc(X4,X3) | ~v1_funct_2(sK4,u1_struct_0(X3),k2_struct_0(sK1)) | k3_tmap_1(X5,sK1,X3,X4,sK4) = k2_partfun1(u1_struct_0(X3),k2_struct_0(sK1),sK4,u1_struct_0(X4)) | ~m1_pre_topc(X3,X5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) )),
% 1.27/0.54    inference(superposition,[],[f134,f144])).
% 1.27/0.54  fof(f134,plain,(
% 1.27/0.54    ( ! [X12,X10,X13,X11] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))) | ~m1_pre_topc(X10,X11) | ~v1_funct_2(sK4,u1_struct_0(X11),u1_struct_0(X12)) | k3_tmap_1(X13,X12,X11,X10,sK4) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK4,u1_struct_0(X10)) | ~m1_pre_topc(X11,X13) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f131,f83])).
% 1.27/0.54  fof(f83,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X2,X0) | ~v2_pre_topc(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f33])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.27/0.54    inference(flattening,[],[f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f12])).
% 1.42/0.54  fof(f12,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.42/0.54  fof(f131,plain,(
% 1.42/0.54    ( ! [X12,X10,X13,X11] : (~m1_pre_topc(X10,X11) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12)))) | ~v1_funct_2(sK4,u1_struct_0(X11),u1_struct_0(X12)) | k3_tmap_1(X13,X12,X11,X10,sK4) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),sK4,u1_struct_0(X10)) | ~m1_pre_topc(X10,X13) | ~m1_pre_topc(X11,X13) | ~l1_pre_topc(X12) | ~v2_pre_topc(X12) | v2_struct_0(X12) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13)) )),
% 1.42/0.54    inference(resolution,[],[f62,f78])).
% 1.42/0.54  fof(f78,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f25])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.54    inference(flattening,[],[f24])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.42/0.54  fof(f62,plain,(
% 1.42/0.54    v1_funct_1(sK4)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    m1_pre_topc(sK3,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f228,plain,(
% 1.42/0.54    m1_pre_topc(sK2,sK3)),
% 1.42/0.54    inference(forward_demodulation,[],[f227,f190])).
% 1.42/0.54  fof(f190,plain,(
% 1.42/0.54    sK3 = g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))),
% 1.42/0.54    inference(backward_demodulation,[],[f65,f187])).
% 1.42/0.54  fof(f65,plain,(
% 1.42/0.54    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f227,plain,(
% 1.42/0.54    m1_pre_topc(sK2,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.42/0.54    inference(forward_demodulation,[],[f219,f187])).
% 1.42/0.54  fof(f219,plain,(
% 1.42/0.54    m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f140,f140,f152,f74])).
% 1.42/0.54  fof(f74,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f46])).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f21])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 1.42/0.54  fof(f152,plain,(
% 1.42/0.54    m1_pre_topc(sK2,sK2)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f140,f73])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f20])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f11])).
% 1.42/0.54  fof(f11,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.42/0.54  fof(f53,plain,(
% 1.42/0.54    v2_pre_topc(sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ~v2_struct_0(sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f941,plain,(
% 1.42/0.54    k3_tmap_1(sK2,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 1.42/0.54    inference(forward_demodulation,[],[f925,f187])).
% 1.42/0.54  fof(f925,plain,(
% 1.42/0.54    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK3,sK2,sK4)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f58,f142,f140,f228,f517,f747])).
% 1.42/0.54  fof(f517,plain,(
% 1.42/0.54    m1_pre_topc(sK3,sK2)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f167,f173,f163])).
% 1.42/0.54  fof(f163,plain,(
% 1.42/0.54    ( ! [X1] : (~m1_pre_topc(X1,sK3) | m1_pre_topc(X1,sK2) | ~l1_pre_topc(X1)) )),
% 1.42/0.54    inference(forward_demodulation,[],[f156,f65])).
% 1.42/0.54  fof(f156,plain,(
% 1.42/0.54    ( ! [X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | m1_pre_topc(X1,sK2) | ~l1_pre_topc(X1)) )),
% 1.42/0.54    inference(resolution,[],[f140,f75])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f46])).
% 1.42/0.54  fof(f173,plain,(
% 1.42/0.54    m1_pre_topc(sK3,sK3)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f167,f73])).
% 1.42/0.54  fof(f142,plain,(
% 1.42/0.54    v2_pre_topc(sK2)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f53,f54,f59,f82])).
% 1.42/0.54  fof(f82,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f31])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ~v2_struct_0(sK2)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f942,plain,(
% 1.42/0.54    k3_tmap_1(sK2,sK1,sK3,sK2,sK4) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.42/0.54    inference(backward_demodulation,[],[f939,f941])).
% 1.42/0.54  fof(f939,plain,(
% 1.42/0.54    k3_tmap_1(sK3,sK1,sK3,sK2,sK4) = k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,k2_struct_0(sK2))),
% 1.42/0.54    inference(forward_demodulation,[],[f927,f187])).
% 1.42/0.54  fof(f927,plain,(
% 1.42/0.54    k2_partfun1(k2_struct_0(sK3),k2_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK3,sK1,sK3,sK2,sK4)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f60,f169,f167,f228,f173,f747])).
% 1.42/0.54  fof(f169,plain,(
% 1.42/0.54    v2_pre_topc(sK3)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f53,f54,f61,f82])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ~v2_struct_0(sK3)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f1063,plain,(
% 1.42/0.54    ~r1_tmap_1(sK2,sK1,k3_tmap_1(sK3,sK1,sK3,sK2,sK4),sK5)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f60,f169,f167,f173,f798,f1054])).
% 1.42/0.54  fof(f1054,plain,(
% 1.42/0.54    ( ! [X2] : (~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5) | ~v1_tsep_1(sK2,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f1053,f58])).
% 1.42/0.54  fof(f1053,plain,(
% 1.42/0.54    ( ! [X2] : (~v1_tsep_1(sK2,X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f1052,f228])).
% 1.42/0.54  fof(f1052,plain,(
% 1.42/0.54    ( ! [X2] : (~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f1048,f191])).
% 1.42/0.54  fof(f191,plain,(
% 1.42/0.54    m1_subset_1(sK5,k2_struct_0(sK2))),
% 1.42/0.54    inference(backward_demodulation,[],[f104,f187])).
% 1.42/0.54  fof(f104,plain,(
% 1.42/0.54    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.42/0.54    inference(forward_demodulation,[],[f67,f68])).
% 1.42/0.54  fof(f67,plain,(
% 1.42/0.54    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f1048,plain,(
% 1.42/0.54    ( ! [X2] : (~m1_subset_1(sK5,k2_struct_0(sK2)) | ~m1_pre_topc(sK2,sK3) | ~v1_tsep_1(sK2,X2) | ~r1_tmap_1(sK2,sK1,k3_tmap_1(X2,sK1,sK3,sK2,sK4),sK5) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.42/0.54    inference(superposition,[],[f1009,f187])).
% 1.42/0.54  fof(f1009,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f1008,f70])).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f1008,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v1_tsep_1(X0,X1) | ~r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5) | r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.42/0.54    inference(resolution,[],[f859,f199])).
% 1.42/0.54  fof(f199,plain,(
% 1.42/0.54    m1_subset_1(sK5,k2_struct_0(sK3))),
% 1.42/0.54    inference(backward_demodulation,[],[f66,f192])).
% 1.42/0.54  fof(f66,plain,(
% 1.42/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f859,plain,(
% 1.42/0.54    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k2_struct_0(sK3)) | ~m1_subset_1(X9,u1_struct_0(X10)) | ~m1_pre_topc(X10,sK3) | ~v1_tsep_1(X10,X11) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9) | r1_tmap_1(sK3,sK1,sK4,X9) | ~m1_pre_topc(sK3,X11) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f858,f60])).
% 1.42/0.54  fof(f858,plain,(
% 1.42/0.54    ( ! [X10,X11,X9] : (~m1_subset_1(X9,u1_struct_0(X10)) | ~m1_subset_1(X9,k2_struct_0(sK3)) | ~m1_pre_topc(X10,sK3) | ~v1_tsep_1(X10,X11) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9) | r1_tmap_1(sK3,sK1,sK4,X9) | ~m1_pre_topc(sK3,X11) | v2_struct_0(sK3) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f857,f198])).
% 1.42/0.54  fof(f857,plain,(
% 1.42/0.54    ( ! [X10,X11,X9] : (~m1_subset_1(X9,u1_struct_0(X10)) | ~m1_subset_1(X9,k2_struct_0(sK3)) | ~m1_pre_topc(X10,sK3) | ~v1_tsep_1(X10,X11) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,X9) | ~m1_pre_topc(sK3,X11) | v2_struct_0(sK3) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f853,f197])).
% 1.42/0.54  fof(f853,plain,(
% 1.42/0.54    ( ! [X10,X11,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK1)))) | ~m1_subset_1(X9,u1_struct_0(X10)) | ~m1_subset_1(X9,k2_struct_0(sK3)) | ~m1_pre_topc(X10,sK3) | ~v1_tsep_1(X10,X11) | ~r1_tmap_1(X10,sK1,k3_tmap_1(X11,sK1,sK3,X10,sK4),X9) | ~v1_funct_2(sK4,k2_struct_0(sK3),k2_struct_0(sK1)) | r1_tmap_1(sK3,sK1,sK4,X9) | ~m1_pre_topc(sK3,X11) | v2_struct_0(sK3) | v2_struct_0(X10) | ~l1_pre_topc(X11) | ~v2_pre_topc(X11) | v2_struct_0(X11)) )),
% 1.42/0.54    inference(superposition,[],[f510,f192])).
% 1.42/0.54  fof(f510,plain,(
% 1.42/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_pre_topc(X6,X4) | ~v1_tsep_1(X6,X7) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | r1_tmap_1(X4,sK1,sK4,X5) | ~m1_pre_topc(X4,X7) | v2_struct_0(X4) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f509,f55])).
% 1.42/0.54  fof(f509,plain,(
% 1.42/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_pre_topc(X6,X4) | ~v1_tsep_1(X6,X7) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | r1_tmap_1(X4,sK1,sK4,X5) | ~m1_pre_topc(X4,X7) | v2_struct_0(X4) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | v2_struct_0(sK1)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f508,f56])).
% 1.42/0.54  fof(f508,plain,(
% 1.42/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_pre_topc(X6,X4) | ~v1_tsep_1(X6,X7) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | r1_tmap_1(X4,sK1,sK4,X5) | ~m1_pre_topc(X4,X7) | v2_struct_0(X4) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f498,f57])).
% 1.42/0.54  fof(f498,plain,(
% 1.42/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),k2_struct_0(sK1)))) | ~m1_subset_1(X5,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_pre_topc(X6,X4) | ~v1_tsep_1(X6,X7) | ~r1_tmap_1(X6,sK1,k3_tmap_1(X7,sK1,X4,X6,sK4),X5) | ~v1_funct_2(sK4,u1_struct_0(X4),k2_struct_0(sK1)) | r1_tmap_1(X4,sK1,sK4,X5) | ~m1_pre_topc(X4,X7) | v2_struct_0(X4) | v2_struct_0(X6) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 1.42/0.54    inference(superposition,[],[f133,f144])).
% 1.42/0.54  fof(f133,plain,(
% 1.42/0.54    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~m1_subset_1(X9,u1_struct_0(X5)) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~m1_pre_topc(X5,X8) | ~v1_tsep_1(X5,X7) | ~r1_tmap_1(X5,X6,k3_tmap_1(X7,X6,X8,X5,sK4),X9) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | r1_tmap_1(X8,X6,sK4,X9) | ~m1_pre_topc(X8,X7) | v2_struct_0(X8) | v2_struct_0(X5) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f130,f83])).
% 1.42/0.54  fof(f130,plain,(
% 1.42/0.54    ( ! [X6,X8,X7,X5,X9] : (~r1_tmap_1(X5,X6,k3_tmap_1(X7,X6,X8,X5,sK4),X9) | ~m1_subset_1(X9,u1_struct_0(X5)) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~m1_pre_topc(X5,X8) | ~m1_pre_topc(X5,X7) | ~v1_tsep_1(X5,X7) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6)))) | ~v1_funct_2(sK4,u1_struct_0(X8),u1_struct_0(X6)) | r1_tmap_1(X8,X6,sK4,X9) | ~m1_pre_topc(X8,X7) | v2_struct_0(X8) | v2_struct_0(X5) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.42/0.54    inference(resolution,[],[f62,f100])).
% 1.42/0.54  fof(f100,plain,(
% 1.42/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | r1_tmap_1(X3,X0,X4,X6) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f91])).
% 1.42/0.54  fof(f91,plain,(
% 1.42/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f80])).
% 1.42/0.54  fof(f80,plain,(
% 1.42/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f47])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f27])).
% 1.42/0.54  fof(f27,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.42/0.54    inference(flattening,[],[f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 1.42/0.54  fof(f798,plain,(
% 1.42/0.54    v1_tsep_1(sK2,sK3)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f169,f167,f173,f695,f373])).
% 1.42/0.54  fof(f373,plain,(
% 1.42/0.54    ( ! [X5] : (~v1_tsep_1(sK3,X5) | ~m1_pre_topc(sK3,X5) | v1_tsep_1(sK2,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(forward_demodulation,[],[f372,f190])).
% 1.42/0.54  fof(f372,plain,(
% 1.42/0.54    ( ! [X5] : (~m1_pre_topc(sK3,X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(forward_demodulation,[],[f371,f190])).
% 1.42/0.54  fof(f371,plain,(
% 1.42/0.54    ( ! [X5] : (~m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f370,f76])).
% 1.42/0.54  fof(f370,plain,(
% 1.42/0.54    ( ! [X5] : (~l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f369,f82])).
% 1.42/0.54  fof(f369,plain,(
% 1.42/0.54    ( ! [X5] : (~l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f368,f142])).
% 1.42/0.54  fof(f368,plain,(
% 1.42/0.54    ( ! [X5] : (~l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f352,f140])).
% 1.42/0.54  fof(f352,plain,(
% 1.42/0.54    ( ! [X5] : (~l1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | ~v1_tsep_1(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)),X5) | v1_tsep_1(sK2,X5) | ~v2_pre_topc(g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 1.42/0.54    inference(superposition,[],[f97,f187])).
% 1.42/0.54  fof(f97,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | v1_tsep_1(X1,X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f89])).
% 1.42/0.54  fof(f89,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f51])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f50])).
% 1.42/0.54  fof(f50,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f37])).
% 1.42/0.54  fof(f37,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f36])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).
% 1.42/0.54  fof(f695,plain,(
% 1.42/0.54    v1_tsep_1(sK3,sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f694,f173])).
% 1.42/0.54  fof(f694,plain,(
% 1.42/0.54    v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f692,f183])).
% 1.42/0.54  fof(f183,plain,(
% 1.42/0.54    v3_pre_topc(k2_struct_0(sK3),sK3)),
% 1.42/0.54    inference(subsumption_resolution,[],[f179,f169])).
% 1.42/0.54  fof(f179,plain,(
% 1.42/0.54    v3_pre_topc(k2_struct_0(sK3),sK3) | ~v2_pre_topc(sK3)),
% 1.42/0.54    inference(resolution,[],[f167,f81])).
% 1.42/0.54  fof(f81,plain,(
% 1.42/0.54    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f28])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 1.42/0.54  fof(f692,plain,(
% 1.42/0.54    ~v3_pre_topc(k2_struct_0(sK3),sK3) | v1_tsep_1(sK3,sK3) | ~m1_pre_topc(sK3,sK3)),
% 1.42/0.54    inference(superposition,[],[f405,f192])).
% 1.42/0.54  fof(f405,plain,(
% 1.42/0.54    ( ! [X2] : (~v3_pre_topc(u1_struct_0(X2),sK3) | v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f404,f402])).
% 1.42/0.54  fof(f402,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X0,sK3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f392,f167])).
% 1.42/0.54  fof(f392,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) )),
% 1.42/0.54    inference(superposition,[],[f77,f192])).
% 1.42/0.54  fof(f77,plain,(
% 1.42/0.54    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.42/0.54  fof(f404,plain,(
% 1.42/0.54    ( ! [X2] : (~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X2),sK3) | v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f403,f169])).
% 1.42/0.54  fof(f403,plain,(
% 1.42/0.54    ( ! [X2] : (~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X2),sK3) | v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~v2_pre_topc(sK3)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f394,f167])).
% 1.42/0.54  fof(f394,plain,(
% 1.42/0.54    ( ! [X2] : (~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(u1_struct_0(X2),sK3) | v1_tsep_1(X2,sK3) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)) )),
% 1.42/0.54    inference(superposition,[],[f94,f192])).
% 1.42/0.54  fof(f94,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f85])).
% 1.42/0.54  fof(f85,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f49])).
% 1.42/0.54  fof(f49,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f48])).
% 1.42/0.54  fof(f48,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f35])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f34])).
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (5388)------------------------------
% 1.42/0.54  % (5388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (5388)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (5388)Memory used [KB]: 7164
% 1.42/0.54  % (5388)Time elapsed: 0.118 s
% 1.42/0.54  % (5388)------------------------------
% 1.42/0.54  % (5388)------------------------------
% 1.42/0.54  % (5372)Success in time 0.176 s
%------------------------------------------------------------------------------
