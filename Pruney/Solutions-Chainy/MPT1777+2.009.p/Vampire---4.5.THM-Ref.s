%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  281 (21143 expanded)
%              Number of leaves         :   28 (10694 expanded)
%              Depth                    :   45
%              Number of atoms          : 1410 (320003 expanded)
%              Number of equality atoms :   79 (43618 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1163,plain,(
    $false ),
    inference(global_subsumption,[],[f78,f71,f70,f69,f1162])).

fof(f1162,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK6,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(resolution,[],[f1161,f129])).

fof(f129,plain,(
    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8) ),
    inference(backward_demodulation,[],[f86,f85])).

fof(f85,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f52])).

% (20881)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f52,plain,
    ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
    & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)
    & sK8 = sK9
    & m1_subset_1(sK9,u1_struct_0(sK5))
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
    & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f19,f51,f50,f49,f48,f47,f46,f45])).

fof(f45,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK4,X4,X5)
                          & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK4,X4,X5)
                        & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK4,X4,X5)
                      & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK5)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK4,X4,X5)
                    & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK5)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK6,sK4,X4,X5)
                  & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK5)) )
              & m1_subset_1(X5,u1_struct_0(sK6)) )
          & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
          & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK6,sK3)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK6,sK4,X4,X5)
                & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK5)) )
            & m1_subset_1(X5,u1_struct_0(sK6)) )
        & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
        & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK6,sK4,sK7,X5)
              & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK5)) )
          & m1_subset_1(X5,u1_struct_0(sK6)) )
      & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))
      & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK6,sK4,sK7,X5)
            & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK5)) )
        & m1_subset_1(X5,u1_struct_0(sK6)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
          & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
          & sK8 = X6
          & m1_subset_1(X6,u1_struct_0(sK5)) )
      & m1_subset_1(sK8,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
        & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6)
        & sK8 = X6
        & m1_subset_1(X6,u1_struct_0(sK5)) )
   => ( ~ r1_tmap_1(sK6,sK4,sK7,sK8)
      & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)
      & sK8 = sK9
      & m1_subset_1(sK9,u1_struct_0(sK5)) ) ),
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

fof(f86,plain,(
    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) ),
    inference(cnf_transformation,[],[f52])).

fof(f1161,plain,(
    ! [X0] :
      ( ~ r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f147,f1159])).

fof(f1159,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(sK5,sK5) ) ),
    inference(resolution,[],[f1157,f221])).

fof(f221,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK6)
      | ~ m1_pre_topc(X0,sK5) ) ),
    inference(global_subsumption,[],[f143,f219])).

fof(f219,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK5)
      | ~ m1_pre_topc(X0,sK5)
      | m1_pre_topc(X0,sK6) ) ),
    inference(resolution,[],[f205,f147])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(X1,sK6) ) ),
    inference(resolution,[],[f197,f184])).

fof(f184,plain,(
    ! [X10,X9] :
      ( ~ m1_pre_topc(X10,sK6)
      | ~ m1_pre_topc(X9,X10)
      | m1_pre_topc(X9,sK6) ) ),
    inference(global_subsumption,[],[f144,f180])).

fof(f180,plain,(
    ! [X10,X9] :
      ( ~ m1_pre_topc(X9,X10)
      | ~ m1_pre_topc(X10,sK6)
      | ~ l1_pre_topc(sK6)
      | m1_pre_topc(X9,sK6) ) ),
    inference(resolution,[],[f117,f158])).

fof(f158,plain,(
    v2_pre_topc(sK6) ),
    inference(resolution,[],[f155,f78])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f71,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(sK3)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f116,f70])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f144,plain,(
    l1_pre_topc(sK6) ),
    inference(resolution,[],[f141,f78])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f108,f71])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f197,plain,(
    ! [X2] :
      ( m1_pre_topc(X2,sK6)
      | ~ m1_pre_topc(X2,sK5)
      | ~ l1_pre_topc(X2) ) ),
    inference(forward_demodulation,[],[f195,f82])).

fof(f82,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f195,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK5)
      | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f106,f143])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f143,plain,(
    l1_pre_topc(sK5) ),
    inference(resolution,[],[f141,f76])).

fof(f76,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f1157,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK5,sK6)
      | v2_struct_0(X0)
      | ~ r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f75,f1024,f1155])).

% (20881)Refutation not found, incomplete strategy% (20881)------------------------------
% (20881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20901)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (20902)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (20899)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (20891)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (20875)Refutation not found, incomplete strategy% (20875)------------------------------
% (20875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20875)Termination reason: Refutation not found, incomplete strategy

% (20875)Memory used [KB]: 10874
% (20875)Time elapsed: 0.138 s
% (20875)------------------------------
% (20875)------------------------------
% (20883)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (20890)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (20893)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (20894)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (20881)Termination reason: Refutation not found, incomplete strategy

% (20881)Memory used [KB]: 6268
% (20881)Time elapsed: 0.118 s
% (20881)------------------------------
% (20881)------------------------------
fof(f1155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK5,sK6)
      | ~ v1_tsep_1(sK5,sK6)
      | ~ r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8)
      | ~ m1_pre_topc(sK6,X0)
      | v2_struct_0(sK5)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f1154,f130])).

fof(f130,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f84,f85])).

fof(f84,plain,(
    m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f52])).

% (20883)Refutation not found, incomplete strategy% (20883)------------------------------
% (20883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20883)Termination reason: Refutation not found, incomplete strategy

% (20883)Memory used [KB]: 1918
% (20883)Time elapsed: 0.153 s
% (20883)------------------------------
% (20883)------------------------------
fof(f1154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK6)
      | ~ v1_tsep_1(X0,sK6)
      | ~ r1_tmap_1(X0,sK4,k3_tmap_1(X1,sK4,sK6,X0,sK7),sK8)
      | ~ m1_pre_topc(sK6,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(global_subsumption,[],[f87,f1153])).

fof(f1153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK8,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK6)
      | ~ v1_tsep_1(X0,sK6)
      | ~ r1_tmap_1(X0,sK4,k3_tmap_1(X1,sK4,sK6,X0,sK7),sK8)
      | r1_tmap_1(sK6,sK4,sK7,sK8)
      | ~ m1_pre_topc(sK6,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f1152,f130])).

fof(f1152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK6)
      | ~ v1_tsep_1(X1,sK6)
      | ~ r1_tmap_1(X1,sK4,k3_tmap_1(X2,sK4,sK6,X1,sK7),X0)
      | r1_tmap_1(sK6,sK4,sK7,X0)
      | ~ m1_pre_topc(sK6,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(global_subsumption,[],[f74,f73,f72,f333,f1150])).

fof(f1150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_pre_topc(X1,sK6)
      | ~ v1_tsep_1(X1,sK6)
      | ~ r1_tmap_1(X1,sK4,k3_tmap_1(X2,sK4,sK6,X1,sK7),X0)
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK4))
      | r1_tmap_1(sK6,sK4,sK7,X0)
      | ~ m1_pre_topc(sK6,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK4)
      | ~ v2_pre_topc(sK4)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f1141,f334])).

fof(f334,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(backward_demodulation,[],[f81,f332])).

fof(f332,plain,(
    u1_struct_0(sK5) = u1_struct_0(sK6) ),
    inference(global_subsumption,[],[f144,f331])).

fof(f331,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f330,f89])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f330,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | u1_struct_0(sK5) = u1_struct_0(sK6) ),
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,
    ( sK6 != sK6
    | u1_struct_0(sK5) = u1_struct_0(sK6)
    | ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(superposition,[],[f325,f173])).

fof(f173,plain,(
    sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(global_subsumption,[],[f144,f172])).

fof(f172,plain,
    ( sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f90,f168])).

fof(f168,plain,(
    v1_pre_topc(sK6) ),
    inference(global_subsumption,[],[f143,f157,f167])).

fof(f167,plain,
    ( v1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(superposition,[],[f114,f82])).

fof(f114,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f157,plain,(
    v2_pre_topc(sK5) ),
    inference(resolution,[],[f155,f76])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f325,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK6
      | u1_struct_0(sK5) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f121,f82])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f81,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f1141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_pre_topc(X2,sK6)
      | ~ v1_tsep_1(X2,sK6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,sK6,X2,sK7),X1)
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(X0))
      | r1_tmap_1(sK6,X0,sK7,X1)
      | ~ m1_pre_topc(sK6,X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(global_subsumption,[],[f77,f1138])).

fof(f1138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ m1_pre_topc(X2,sK6)
      | ~ v1_tsep_1(X2,sK6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,sK6,X2,sK7),X1)
      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(X0))
      | r1_tmap_1(sK6,X0,sK7,X1)
      | ~ m1_pre_topc(sK6,X3)
      | v2_struct_0(sK6)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f1094,f332])).

fof(f1094,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X0,X3)
      | ~ v1_tsep_1(X0,X3)
      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK7),X4)
      | ~ v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,sK7,X4)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f131,f79])).

fof(f79,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f123,f117])).

fof(f123,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
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
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
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
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f77,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f333,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(backward_demodulation,[],[f80,f332])).

fof(f80,plain,(
    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f73,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f74,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ~ r1_tmap_1(sK6,sK4,sK7,sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f1024,plain,
    ( v1_tsep_1(sK5,sK6)
    | ~ m1_pre_topc(sK5,sK6) ),
    inference(subsumption_resolution,[],[f522,f1019])).

fof(f1019,plain,(
    v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(subsumption_resolution,[],[f739,f1013])).

fof(f1013,plain,(
    v1_tsep_1(sK6,sK6) ),
    inference(subsumption_resolution,[],[f801,f1009])).

fof(f1009,plain,(
    v1_tsep_1(sK5,sK5) ),
    inference(subsumption_resolution,[],[f507,f1002])).

fof(f1002,plain,(
    sP1(sK6) ),
    inference(subsumption_resolution,[],[f922,f994])).

fof(f994,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f700,f983])).

fof(f983,plain,(
    sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f982])).

fof(f982,plain,
    ( sP0(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f981,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK11(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0))
          & r2_hidden(sK12(X0),u1_pre_topc(X0))
          & r2_hidden(sK11(X0),u1_pre_topc(X0))
          & m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK11(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK11(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0))
        & r2_hidden(sK12(X0),u1_pre_topc(X0))
        & r2_hidden(sK11(X0),u1_pre_topc(X0))
        & m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f981,plain,
    ( ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f980])).

fof(f980,plain,
    ( ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f979,f103])).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(sK12(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f979,plain,
    ( ~ r2_hidden(sK12(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f978])).

fof(f978,plain,
    ( ~ r2_hidden(sK12(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f977,f100])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f977,plain,
    ( ~ m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK12(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f976])).

fof(f976,plain,
    ( ~ r2_hidden(sK12(sK5),u1_pre_topc(sK5))
    | ~ m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5)
    | sP0(sK5) ),
    inference(resolution,[],[f917,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f917,plain,
    ( ~ m1_subset_1(sK12(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK12(sK5),u1_pre_topc(sK5))
    | ~ m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK11(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(resolution,[],[f915,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f915,plain,(
    ! [X2,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X3,X2),u1_pre_topc(sK5))
      | ~ r2_hidden(X2,u1_pre_topc(sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r2_hidden(X3,u1_pre_topc(sK5)) ) ),
    inference(global_subsumption,[],[f144,f158,f914])).

fof(f914,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,u1_pre_topc(sK5))
      | r2_hidden(k9_subset_1(u1_struct_0(sK5),X3,X2),u1_pre_topc(sK5))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r2_hidden(X3,u1_pre_topc(sK5))
      | ~ l1_pre_topc(sK6)
      | ~ v2_pre_topc(sK6) ) ),
    inference(resolution,[],[f890,f138])).

fof(f138,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f136,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
        & r1_tarski(sK10(X0),u1_pre_topc(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( sP1(X0)
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
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ( sP0(X0)
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f136,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f91,f105])).

fof(f105,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f43,f42,f41])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f91,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v2_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f890,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK6)
      | ~ r2_hidden(X1,u1_pre_topc(sK5))
      | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r2_hidden(X0,u1_pre_topc(sK5)) ) ),
    inference(forward_demodulation,[],[f889,f461])).

fof(f461,plain,(
    u1_pre_topc(sK5) = u1_pre_topc(sK6) ),
    inference(trivial_inequality_removal,[],[f459])).

fof(f459,plain,
    ( sK6 != sK6
    | u1_pre_topc(sK5) = u1_pre_topc(sK6) ),
    inference(superposition,[],[f458,f82])).

fof(f458,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != sK6
      | u1_pre_topc(sK6) = X3 ) ),
    inference(global_subsumption,[],[f365,f454])).

fof(f454,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X2,X3) != sK6
      | u1_pre_topc(sK6) = X3
      | ~ m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ) ),
    inference(superposition,[],[f122,f336])).

fof(f336,plain,(
    sK6 = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK6)) ),
    inference(backward_demodulation,[],[f173,f332])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

% (20888)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f365,plain,(
    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(global_subsumption,[],[f144,f344])).

fof(f344,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK6) ),
    inference(superposition,[],[f89,f332])).

fof(f889,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(sK5))
      | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5))
      | ~ r2_hidden(X0,u1_pre_topc(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ sP0(sK6) ) ),
    inference(forward_demodulation,[],[f888,f461])).

fof(f888,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5))
      | ~ r2_hidden(X1,u1_pre_topc(sK6))
      | ~ r2_hidden(X0,u1_pre_topc(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ sP0(sK6) ) ),
    inference(forward_demodulation,[],[f885,f461])).

fof(f885,plain,(
    ! [X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK6))
      | ~ r2_hidden(X1,u1_pre_topc(sK6))
      | ~ r2_hidden(X0,u1_pre_topc(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ sP0(sK6) ) ),
    inference(superposition,[],[f99,f332])).

fof(f99,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f700,plain,
    ( sP1(sK5)
    | ~ sP0(sK5) ),
    inference(global_subsumption,[],[f144,f158,f699])).

fof(f699,plain,
    ( sP1(sK5)
    | ~ sP0(sK5)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f697,f136])).

fof(f697,plain,
    ( ~ sP1(sK6)
    | sP1(sK5)
    | ~ sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( sP1(sK5)
    | ~ sP1(sK6)
    | ~ sP0(sK5)
    | ~ sP1(sK6) ),
    inference(resolution,[],[f688,f469])).

fof(f469,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP1(sK6) ),
    inference(backward_demodulation,[],[f345,f461])).

fof(f345,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | ~ sP1(sK6) ),
    inference(superposition,[],[f93,f332])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f688,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | sP1(sK5)
    | ~ sP1(sK6)
    | ~ sP0(sK5) ),
    inference(duplicate_literal_removal,[],[f687])).

fof(f687,plain,
    ( ~ sP0(sK5)
    | sP1(sK5)
    | ~ sP1(sK6)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(resolution,[],[f686,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(sK10(X0),u1_pre_topc(X0))
      | ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f686,plain,
    ( ~ r1_tarski(sK10(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ sP1(sK6)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( ~ r1_tarski(sK10(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ sP1(sK6)
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(resolution,[],[f667,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f667,plain,
    ( ~ m1_subset_1(sK10(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r1_tarski(sK10(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ sP1(sK6) ),
    inference(resolution,[],[f664,f633])).

fof(f633,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK5)),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sP1(sK5)
    | ~ sP1(sK6) ),
    inference(resolution,[],[f98,f469])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f664,plain,(
    ! [X1] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),X1),u1_pre_topc(sK5))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
      | ~ r1_tarski(X1,u1_pre_topc(sK5)) ) ),
    inference(global_subsumption,[],[f144,f158,f663])).

fof(f663,plain,(
    ! [X1] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),X1),u1_pre_topc(sK5))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
      | ~ r1_tarski(X1,u1_pre_topc(sK5))
      | ~ v2_pre_topc(sK6)
      | ~ l1_pre_topc(sK6) ) ),
    inference(resolution,[],[f657,f136])).

fof(f657,plain,(
    ! [X0] :
      ( ~ sP1(sK6)
      | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
      | ~ r1_tarski(X0,u1_pre_topc(sK5)) ) ),
    inference(forward_demodulation,[],[f656,f461])).

fof(f656,plain,(
    ! [X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5))
      | ~ r1_tarski(X0,u1_pre_topc(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
      | ~ sP1(sK6) ) ),
    inference(forward_demodulation,[],[f653,f461])).

fof(f653,plain,(
    ! [X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK6))
      | ~ r1_tarski(X0,u1_pre_topc(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
      | ~ sP1(sK6) ) ),
    inference(superposition,[],[f94,f332])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f922,plain,
    ( sP1(sK6)
    | ~ sP1(sK5) ),
    inference(subsumption_resolution,[],[f655,f918])).

% (20882)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f918,plain,(
    sP0(sK6) ),
    inference(global_subsumption,[],[f346,f347,f486,f487,f916])).

fof(f916,plain,
    ( ~ r2_hidden(sK12(sK6),u1_pre_topc(sK5))
    | ~ m1_subset_1(sK12(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK11(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK11(sK6),u1_pre_topc(sK5))
    | sP0(sK6) ),
    inference(resolution,[],[f915,f470])).

fof(f470,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK11(sK6),sK12(sK6)),u1_pre_topc(sK5))
    | sP0(sK6) ),
    inference(backward_demodulation,[],[f348,f461])).

fof(f348,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK5),sK11(sK6),sK12(sK6)),u1_pre_topc(sK6))
    | sP0(sK6) ),
    inference(superposition,[],[f104,f332])).

fof(f487,plain,
    ( r2_hidden(sK12(sK6),u1_pre_topc(sK5))
    | sP0(sK6) ),
    inference(superposition,[],[f103,f461])).

fof(f486,plain,
    ( r2_hidden(sK11(sK6),u1_pre_topc(sK5))
    | sP0(sK6) ),
    inference(superposition,[],[f102,f461])).

fof(f347,plain,
    ( m1_subset_1(sK12(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK6) ),
    inference(superposition,[],[f101,f332])).

fof(f346,plain,
    ( m1_subset_1(sK11(sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK6) ),
    inference(superposition,[],[f100,f332])).

fof(f655,plain,
    ( sP1(sK6)
    | ~ sP1(sK5)
    | ~ sP0(sK6) ),
    inference(global_subsumption,[],[f472,f493,f516,f576,f650])).

fof(f650,plain,
    ( ~ r1_tarski(sK10(sK6),u1_pre_topc(sK5))
    | ~ m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP1(sK5)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | sP1(sK6) ),
    inference(resolution,[],[f94,f644])).

fof(f644,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | sP1(sK6) ),
    inference(forward_demodulation,[],[f643,f461])).

fof(f643,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK6))
    | sP1(sK6) ),
    inference(forward_demodulation,[],[f639,f461])).

fof(f639,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | ~ sP0(sK6)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK6))
    | sP1(sK6) ),
    inference(superposition,[],[f98,f332])).

fof(f576,plain,
    ( m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | sP1(sK6) ),
    inference(forward_demodulation,[],[f575,f461])).

fof(f575,plain,
    ( m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK6)
    | sP1(sK6)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) ),
    inference(superposition,[],[f96,f332])).

fof(f516,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6)
    | ~ sP1(sK5) ),
    inference(resolution,[],[f473,f93])).

fof(f473,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v3_pre_topc(u1_struct_0(sK5),sK6) ),
    inference(backward_demodulation,[],[f378,f461])).

fof(f378,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | v3_pre_topc(u1_struct_0(sK5),sK6) ),
    inference(global_subsumption,[],[f149,f364])).

fof(f364,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | v3_pre_topc(u1_struct_0(sK5),sK6)
    | ~ m1_pre_topc(sK6,sK6) ),
    inference(superposition,[],[f306,f332])).

fof(f306,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6))
      | v3_pre_topc(u1_struct_0(X0),sK6)
      | ~ m1_pre_topc(X0,sK6) ) ),
    inference(global_subsumption,[],[f144,f303])).

fof(f303,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6))
      | v3_pre_topc(u1_struct_0(X0),sK6)
      | ~ m1_pre_topc(X0,sK6)
      | ~ l1_pre_topc(sK6) ) ),
    inference(resolution,[],[f257,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f257,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ r2_hidden(X3,u1_pre_topc(sK6))
      | v3_pre_topc(X3,sK6) ) ),
    inference(resolution,[],[f111,f144])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f149,plain,(
    m1_pre_topc(sK6,sK6) ),
    inference(resolution,[],[f144,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f493,plain,
    ( r1_tarski(sK10(sK6),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | sP1(sK6) ),
    inference(forward_demodulation,[],[f485,f332])).

fof(f485,plain,
    ( r1_tarski(sK10(sK6),u1_pre_topc(sK5))
    | ~ sP0(sK6)
    | sP1(sK6)
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5)) ),
    inference(superposition,[],[f97,f461])).

fof(f472,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK6) ),
    inference(backward_demodulation,[],[f372,f461])).

fof(f372,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK6) ),
    inference(global_subsumption,[],[f149,f356])).

fof(f356,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK6)
    | ~ m1_pre_topc(sK6,sK6) ),
    inference(superposition,[],[f253,f332])).

fof(f253,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6))
      | ~ v3_pre_topc(u1_struct_0(X0),sK6)
      | ~ m1_pre_topc(X0,sK6) ) ),
    inference(global_subsumption,[],[f144,f250])).

fof(f250,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(X0),sK6)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6))
      | ~ m1_pre_topc(X0,sK6)
      | ~ l1_pre_topc(sK6) ) ),
    inference(resolution,[],[f237,f109])).

fof(f237,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v3_pre_topc(X3,sK6)
      | r2_hidden(X3,u1_pre_topc(sK6)) ) ),
    inference(resolution,[],[f110,f144])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f507,plain,
    ( v1_tsep_1(sK5,sK5)
    | ~ sP1(sK6) ),
    inference(global_subsumption,[],[f147,f506])).

fof(f506,plain,
    ( ~ sP1(sK6)
    | ~ m1_pre_topc(sK5,sK5)
    | v1_tsep_1(sK5,sK5) ),
    inference(resolution,[],[f503,f285])).

fof(f285,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(u1_struct_0(X4),sK5)
      | ~ m1_pre_topc(X4,sK5)
      | v1_tsep_1(X4,sK5) ) ),
    inference(global_subsumption,[],[f143,f281])).

fof(f281,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(u1_struct_0(X4),sK5)
      | ~ m1_pre_topc(X4,sK5)
      | ~ l1_pre_topc(sK5)
      | v1_tsep_1(X4,sK5) ) ),
    inference(resolution,[],[f133,f157])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(global_subsumption,[],[f109,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f503,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5)
    | ~ sP1(sK6) ),
    inference(resolution,[],[f469,f377])).

% (20898)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f377,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(global_subsumption,[],[f212,f363])).

fof(f363,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v3_pre_topc(u1_struct_0(sK5),sK5)
    | ~ m1_pre_topc(sK6,sK5) ),
    inference(superposition,[],[f298,f332])).

fof(f298,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5))
      | v3_pre_topc(u1_struct_0(X0),sK5)
      | ~ m1_pre_topc(X0,sK5) ) ),
    inference(global_subsumption,[],[f143,f295])).

fof(f295,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5))
      | v3_pre_topc(u1_struct_0(X0),sK5)
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(resolution,[],[f256,f109])).

fof(f256,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r2_hidden(X2,u1_pre_topc(sK5))
      | v3_pre_topc(X2,sK5) ) ),
    inference(resolution,[],[f111,f143])).

fof(f212,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(global_subsumption,[],[f144,f209])).

fof(f209,plain,
    ( m1_pre_topc(sK6,sK5)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f203,f149])).

fof(f203,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK6)
      | m1_pre_topc(X2,sK5)
      | ~ l1_pre_topc(X2) ) ),
    inference(forward_demodulation,[],[f201,f82])).

fof(f201,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      | m1_pre_topc(X2,sK5)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f107,f143])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f801,plain,
    ( v1_tsep_1(sK6,sK6)
    | ~ v1_tsep_1(sK5,sK5) ),
    inference(global_subsumption,[],[f147,f795])).

fof(f795,plain,
    ( ~ v1_tsep_1(sK5,sK5)
    | ~ m1_pre_topc(sK5,sK5)
    | v1_tsep_1(sK6,sK6) ),
    inference(resolution,[],[f776,f521])).

fof(f521,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK5)
    | v1_tsep_1(sK6,sK6) ),
    inference(resolution,[],[f514,f376])).

fof(f376,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK6)
    | v1_tsep_1(sK6,sK6) ),
    inference(global_subsumption,[],[f149,f362])).

fof(f362,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | v1_tsep_1(sK6,sK6) ),
    inference(superposition,[],[f286,f332])).

fof(f286,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(u1_struct_0(X5),sK6)
      | ~ m1_pre_topc(X5,sK6)
      | v1_tsep_1(X5,sK6) ) ),
    inference(global_subsumption,[],[f144,f282])).

fof(f282,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(u1_struct_0(X5),sK6)
      | ~ m1_pre_topc(X5,sK6)
      | ~ l1_pre_topc(sK6)
      | v1_tsep_1(X5,sK6) ) ),
    inference(resolution,[],[f133,f158])).

fof(f514,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6)
    | ~ v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(resolution,[],[f473,f371])).

% (20887)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f371,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(global_subsumption,[],[f212,f355])).

fof(f355,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ v3_pre_topc(u1_struct_0(sK5),sK5)
    | ~ m1_pre_topc(sK6,sK5) ),
    inference(superposition,[],[f249,f332])).

fof(f249,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5))
      | ~ v3_pre_topc(u1_struct_0(X0),sK5)
      | ~ m1_pre_topc(X0,sK5) ) ),
    inference(global_subsumption,[],[f143,f246])).

fof(f246,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(X0),sK5)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5))
      | ~ m1_pre_topc(X0,sK5)
      | ~ l1_pre_topc(sK5) ) ),
    inference(resolution,[],[f236,f109])).

fof(f236,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v3_pre_topc(X2,sK5)
      | r2_hidden(X2,u1_pre_topc(sK5)) ) ),
    inference(resolution,[],[f110,f143])).

fof(f776,plain,(
    ! [X4] :
      ( v3_pre_topc(u1_struct_0(X4),sK5)
      | ~ v1_tsep_1(X4,sK5)
      | ~ m1_pre_topc(X4,sK5) ) ),
    inference(global_subsumption,[],[f143,f772])).

fof(f772,plain,(
    ! [X4] :
      ( ~ v1_tsep_1(X4,sK5)
      | v3_pre_topc(u1_struct_0(X4),sK5)
      | ~ l1_pre_topc(sK5)
      | ~ m1_pre_topc(X4,sK5) ) ),
    inference(resolution,[],[f716,f157])).

fof(f716,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v1_tsep_1(X0,X1)
      | v3_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f709])).

fof(f709,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v1_tsep_1(X0,X1)
      | v3_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f128,f109])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f739,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5)
    | ~ v1_tsep_1(sK6,sK6) ),
    inference(global_subsumption,[],[f144,f149,f158,f726])).

fof(f726,plain,
    ( ~ v1_tsep_1(sK6,sK6)
    | ~ m1_pre_topc(sK6,sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(resolution,[],[f717,f509])).

fof(f509,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK6)
    | v3_pre_topc(u1_struct_0(sK5),sK5) ),
    inference(resolution,[],[f472,f377])).

fof(f717,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(sK5),X0)
      | ~ v1_tsep_1(sK6,X0)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(global_subsumption,[],[f350,f713])).

fof(f713,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK6,X0)
      | ~ v1_tsep_1(sK6,X0)
      | v3_pre_topc(u1_struct_0(sK5),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(superposition,[],[f128,f332])).

fof(f350,plain,(
    ! [X1] :
      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(sK6,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f109,f332])).

fof(f522,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK5),sK5)
    | ~ m1_pre_topc(sK5,sK6)
    | v1_tsep_1(sK5,sK6) ),
    inference(resolution,[],[f514,f286])).

fof(f75,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f147,plain,(
    m1_pre_topc(sK5,sK5) ),
    inference(resolution,[],[f143,f88])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.46  % (20889)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.48  % (20897)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.49  % (20880)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (20896)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (20884)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.51  % (20885)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.52  % (20875)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.52  % (20889)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.53  % (20900)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.53  % (20876)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (20877)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.53  % (20892)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f1163,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(global_subsumption,[],[f78,f71,f70,f69,f1162])).
% 0.19/0.53  fof(f1162,plain,(
% 0.19/0.53    v2_struct_0(sK3) | ~m1_pre_topc(sK6,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3)),
% 0.19/0.53    inference(resolution,[],[f1161,f129])).
% 0.19/0.53  fof(f129,plain,(
% 0.19/0.53    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK8)),
% 0.19/0.53    inference(backward_demodulation,[],[f86,f85])).
% 0.19/0.53  fof(f85,plain,(
% 0.19/0.53    sK8 = sK9),
% 0.19/0.53    inference(cnf_transformation,[],[f52])).
% 0.19/0.53  % (20881)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ((((((~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK5))) & m1_subset_1(sK8,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(sK7)) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f19,f51,f50,f49,f48,f47,f46,f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK3,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(X2,sK4,k3_tmap_1(sK3,sK4,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,X3,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(X4)) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,X4,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4)) & v1_funct_1(sK7))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    ? [X5] : (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,X5) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(X5,u1_struct_0(sK6))) => (? [X6] : (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & sK8 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) & m1_subset_1(sK8,u1_struct_0(sK6)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    ? [X6] : (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),X6) & sK8 = X6 & m1_subset_1(X6,u1_struct_0(sK5))) => (~r1_tmap_1(sK6,sK4,sK7,sK8) & r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK5)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.53    inference(flattening,[],[f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,negated_conjecture,(
% 0.19/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.19/0.53    inference(negated_conjecture,[],[f15])).
% 0.19/0.53  fof(f15,conjecture,(
% 0.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.19/0.53  fof(f86,plain,(
% 0.19/0.53    r1_tmap_1(sK5,sK4,k3_tmap_1(sK3,sK4,sK6,sK5,sK7),sK9)),
% 0.19/0.53    inference(cnf_transformation,[],[f52])).
% 0.19/0.54  fof(f1161,plain,(
% 0.19/0.54    ( ! [X0] : (~r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8) | v2_struct_0(X0) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.54    inference(global_subsumption,[],[f147,f1159])).
% 0.19/0.54  fof(f1159,plain,(
% 0.19/0.54    ( ! [X0] : (v2_struct_0(X0) | ~r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK5,sK5)) )),
% 0.19/0.54    inference(resolution,[],[f1157,f221])).
% 0.19/0.54  fof(f221,plain,(
% 0.19/0.54    ( ! [X0] : (m1_pre_topc(X0,sK6) | ~m1_pre_topc(X0,sK5)) )),
% 0.19/0.54    inference(global_subsumption,[],[f143,f219])).
% 0.19/0.54  fof(f219,plain,(
% 0.19/0.54    ( ! [X0] : (~l1_pre_topc(sK5) | ~m1_pre_topc(X0,sK5) | m1_pre_topc(X0,sK6)) )),
% 0.19/0.54    inference(resolution,[],[f205,f147])).
% 0.19/0.54  fof(f205,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK5) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_pre_topc(X1,sK6)) )),
% 0.19/0.54    inference(resolution,[],[f197,f184])).
% 0.19/0.54  fof(f184,plain,(
% 0.19/0.54    ( ! [X10,X9] : (~m1_pre_topc(X10,sK6) | ~m1_pre_topc(X9,X10) | m1_pre_topc(X9,sK6)) )),
% 0.19/0.54    inference(global_subsumption,[],[f144,f180])).
% 0.19/0.54  fof(f180,plain,(
% 0.19/0.54    ( ! [X10,X9] : (~m1_pre_topc(X9,X10) | ~m1_pre_topc(X10,sK6) | ~l1_pre_topc(sK6) | m1_pre_topc(X9,sK6)) )),
% 0.19/0.54    inference(resolution,[],[f117,f158])).
% 0.19/0.54  fof(f158,plain,(
% 0.19/0.54    v2_pre_topc(sK6)),
% 0.19/0.54    inference(resolution,[],[f155,f78])).
% 0.19/0.54  fof(f155,plain,(
% 0.19/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_pre_topc(X0)) )),
% 0.19/0.54    inference(global_subsumption,[],[f71,f153])).
% 0.19/0.54  fof(f153,plain,(
% 0.19/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3) | v2_pre_topc(X0)) )),
% 0.19/0.54    inference(resolution,[],[f116,f70])).
% 0.19/0.54  fof(f116,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f35])).
% 0.19/0.54  fof(f35,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.19/0.54  fof(f117,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X2,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,axiom,(
% 0.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.19/0.54  fof(f144,plain,(
% 0.19/0.54    l1_pre_topc(sK6)),
% 0.19/0.54    inference(resolution,[],[f141,f78])).
% 0.19/0.54  fof(f141,plain,(
% 0.19/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | l1_pre_topc(X0)) )),
% 0.19/0.54    inference(resolution,[],[f108,f71])).
% 0.19/0.54  fof(f108,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f27])).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.54  fof(f197,plain,(
% 0.19/0.54    ( ! [X2] : (m1_pre_topc(X2,sK6) | ~m1_pre_topc(X2,sK5) | ~l1_pre_topc(X2)) )),
% 0.19/0.54    inference(forward_demodulation,[],[f195,f82])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6),
% 0.19/0.54    inference(cnf_transformation,[],[f52])).
% 0.19/0.54  fof(f195,plain,(
% 0.19/0.54    ( ! [X2] : (~m1_pre_topc(X2,sK5) | m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | ~l1_pre_topc(X2)) )),
% 0.19/0.54    inference(resolution,[],[f106,f143])).
% 0.19/0.54  fof(f106,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f64])).
% 0.19/0.54  fof(f64,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(nnf_transformation,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.19/0.54  fof(f143,plain,(
% 0.19/0.54    l1_pre_topc(sK5)),
% 0.19/0.54    inference(resolution,[],[f141,f76])).
% 0.19/0.54  fof(f76,plain,(
% 0.19/0.54    m1_pre_topc(sK5,sK3)),
% 0.19/0.54    inference(cnf_transformation,[],[f52])).
% 0.19/0.54  fof(f1157,plain,(
% 0.19/0.54    ( ! [X0] : (~m1_pre_topc(sK5,sK6) | v2_struct_0(X0) | ~r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.54    inference(global_subsumption,[],[f75,f1024,f1155])).
% 0.19/0.54  % (20881)Refutation not found, incomplete strategy% (20881)------------------------------
% 0.19/0.54  % (20881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (20901)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.54  % (20902)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.54  % (20899)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.54  % (20891)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.54  % (20875)Refutation not found, incomplete strategy% (20875)------------------------------
% 0.19/0.54  % (20875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (20875)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (20875)Memory used [KB]: 10874
% 0.19/0.54  % (20875)Time elapsed: 0.138 s
% 0.19/0.54  % (20875)------------------------------
% 0.19/0.54  % (20875)------------------------------
% 0.19/0.54  % (20883)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.55  % (20890)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.55  % (20893)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.55  % (20894)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.55  % (20881)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (20881)Memory used [KB]: 6268
% 0.19/0.55  % (20881)Time elapsed: 0.118 s
% 0.19/0.55  % (20881)------------------------------
% 0.19/0.55  % (20881)------------------------------
% 0.19/0.55  fof(f1155,plain,(
% 0.19/0.55    ( ! [X0] : (~m1_pre_topc(sK5,sK6) | ~v1_tsep_1(sK5,sK6) | ~r1_tmap_1(sK5,sK4,k3_tmap_1(X0,sK4,sK6,sK5,sK7),sK8) | ~m1_pre_topc(sK6,X0) | v2_struct_0(sK5) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.55    inference(resolution,[],[f1154,f130])).
% 0.19/0.55  fof(f130,plain,(
% 0.19/0.55    m1_subset_1(sK8,u1_struct_0(sK5))),
% 0.19/0.55    inference(forward_demodulation,[],[f84,f85])).
% 0.19/0.55  fof(f84,plain,(
% 0.19/0.55    m1_subset_1(sK9,u1_struct_0(sK5))),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  % (20883)Refutation not found, incomplete strategy% (20883)------------------------------
% 0.19/0.55  % (20883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (20883)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (20883)Memory used [KB]: 1918
% 0.19/0.55  % (20883)Time elapsed: 0.153 s
% 0.19/0.55  % (20883)------------------------------
% 0.19/0.55  % (20883)------------------------------
% 0.19/0.55  fof(f1154,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~m1_subset_1(sK8,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK6) | ~v1_tsep_1(X0,sK6) | ~r1_tmap_1(X0,sK4,k3_tmap_1(X1,sK4,sK6,X0,sK7),sK8) | ~m1_pre_topc(sK6,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.19/0.55    inference(global_subsumption,[],[f87,f1153])).
% 0.19/0.55  fof(f1153,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~m1_subset_1(sK8,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK6) | ~v1_tsep_1(X0,sK6) | ~r1_tmap_1(X0,sK4,k3_tmap_1(X1,sK4,sK6,X0,sK7),sK8) | r1_tmap_1(sK6,sK4,sK7,sK8) | ~m1_pre_topc(sK6,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.19/0.55    inference(resolution,[],[f1152,f130])).
% 0.19/0.55  fof(f1152,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_pre_topc(X1,sK6) | ~v1_tsep_1(X1,sK6) | ~r1_tmap_1(X1,sK4,k3_tmap_1(X2,sK4,sK6,X1,sK7),X0) | r1_tmap_1(sK6,sK4,sK7,X0) | ~m1_pre_topc(sK6,X2) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.19/0.55    inference(global_subsumption,[],[f74,f73,f72,f333,f1150])).
% 0.19/0.55  fof(f1150,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_pre_topc(X1,sK6) | ~v1_tsep_1(X1,sK6) | ~r1_tmap_1(X1,sK4,k3_tmap_1(X2,sK4,sK6,X1,sK7),X0) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK4)) | r1_tmap_1(sK6,sK4,sK7,X0) | ~m1_pre_topc(sK6,X2) | v2_struct_0(X1) | ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.19/0.55    inference(resolution,[],[f1141,f334])).
% 0.19/0.55  fof(f334,plain,(
% 0.19/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 0.19/0.55    inference(backward_demodulation,[],[f81,f332])).
% 0.19/0.55  fof(f332,plain,(
% 0.19/0.55    u1_struct_0(sK5) = u1_struct_0(sK6)),
% 0.19/0.55    inference(global_subsumption,[],[f144,f331])).
% 0.19/0.55  fof(f331,plain,(
% 0.19/0.55    u1_struct_0(sK5) = u1_struct_0(sK6) | ~l1_pre_topc(sK6)),
% 0.19/0.55    inference(resolution,[],[f330,f89])).
% 0.19/0.55  fof(f89,plain,(
% 0.19/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f21])).
% 0.19/0.55  fof(f21,plain,(
% 0.19/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f6])).
% 0.19/0.55  fof(f6,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.55  fof(f330,plain,(
% 0.19/0.55    ~m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) | u1_struct_0(sK5) = u1_struct_0(sK6)),
% 0.19/0.55    inference(trivial_inequality_removal,[],[f329])).
% 0.19/0.55  fof(f329,plain,(
% 0.19/0.55    sK6 != sK6 | u1_struct_0(sK5) = u1_struct_0(sK6) | ~m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))),
% 0.19/0.55    inference(superposition,[],[f325,f173])).
% 0.19/0.55  fof(f173,plain,(
% 0.19/0.55    sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))),
% 0.19/0.55    inference(global_subsumption,[],[f144,f172])).
% 0.19/0.55  fof(f172,plain,(
% 0.19/0.55    sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | ~l1_pre_topc(sK6)),
% 0.19/0.55    inference(resolution,[],[f90,f168])).
% 0.19/0.55  fof(f168,plain,(
% 0.19/0.55    v1_pre_topc(sK6)),
% 0.19/0.55    inference(global_subsumption,[],[f143,f157,f167])).
% 0.19/0.55  fof(f167,plain,(
% 0.19/0.55    v1_pre_topc(sK6) | ~l1_pre_topc(sK5) | ~v2_pre_topc(sK5)),
% 0.19/0.55    inference(superposition,[],[f114,f82])).
% 0.19/0.55  fof(f114,plain,(
% 0.19/0.55    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f33])).
% 0.19/0.55  fof(f33,plain,(
% 0.19/0.55    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f32])).
% 0.19/0.55  fof(f32,plain,(
% 0.19/0.55    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f7])).
% 0.19/0.55  fof(f7,axiom,(
% 0.19/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 0.19/0.55  fof(f157,plain,(
% 0.19/0.55    v2_pre_topc(sK5)),
% 0.19/0.55    inference(resolution,[],[f155,f76])).
% 0.19/0.55  fof(f90,plain,(
% 0.19/0.55    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f23])).
% 0.19/0.55  fof(f23,plain,(
% 0.19/0.55    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f22])).
% 0.19/0.55  fof(f22,plain,(
% 0.19/0.55    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f1])).
% 0.19/0.55  fof(f1,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.19/0.55  fof(f325,plain,(
% 0.19/0.55    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != sK6 | u1_struct_0(sK5) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.55    inference(superposition,[],[f121,f82])).
% 0.19/0.55  fof(f121,plain,(
% 0.19/0.55    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f40])).
% 0.19/0.55  fof(f40,plain,(
% 0.19/0.55    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.55    inference(ennf_transformation,[],[f8])).
% 0.19/0.55  fof(f8,axiom,(
% 0.19/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.19/0.55  fof(f81,plain,(
% 0.19/0.55    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK4))))),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f1141,plain,(
% 0.19/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~m1_pre_topc(X2,sK6) | ~v1_tsep_1(X2,sK6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,sK6,X2,sK7),X1) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(X0)) | r1_tmap_1(sK6,X0,sK7,X1) | ~m1_pre_topc(sK6,X3) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.19/0.55    inference(global_subsumption,[],[f77,f1138])).
% 0.19/0.55  fof(f1138,plain,(
% 0.19/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~m1_pre_topc(X2,sK6) | ~v1_tsep_1(X2,sK6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,sK6,X2,sK7),X1) | ~v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(X0)) | r1_tmap_1(sK6,X0,sK7,X1) | ~m1_pre_topc(sK6,X3) | v2_struct_0(sK6) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) )),
% 0.19/0.55    inference(superposition,[],[f1094,f332])).
% 0.19/0.55  fof(f1094,plain,(
% 0.19/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X0,X3) | ~v1_tsep_1(X0,X3) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK7),X4) | ~v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,sK7,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.19/0.55    inference(resolution,[],[f131,f79])).
% 0.19/0.55  fof(f79,plain,(
% 0.19/0.55    v1_funct_1(sK7)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f131,plain,(
% 0.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X6) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.55    inference(subsumption_resolution,[],[f123,f117])).
% 0.19/0.55  fof(f123,plain,(
% 0.19/0.55    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.55    inference(equality_resolution,[],[f113])).
% 0.19/0.55  fof(f113,plain,(
% 0.19/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f66])).
% 0.19/0.55  fof(f66,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.55    inference(nnf_transformation,[],[f31])).
% 0.19/0.55  fof(f31,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.55    inference(flattening,[],[f30])).
% 0.19/0.55  fof(f30,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f14])).
% 0.19/0.55  fof(f14,axiom,(
% 0.19/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.19/0.55  fof(f77,plain,(
% 0.19/0.55    ~v2_struct_0(sK6)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f333,plain,(
% 0.19/0.55    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK4))),
% 0.19/0.55    inference(backward_demodulation,[],[f80,f332])).
% 0.19/0.55  fof(f80,plain,(
% 0.19/0.55    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK4))),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f72,plain,(
% 0.19/0.55    ~v2_struct_0(sK4)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f73,plain,(
% 0.19/0.55    v2_pre_topc(sK4)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f74,plain,(
% 0.19/0.55    l1_pre_topc(sK4)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f87,plain,(
% 0.19/0.55    ~r1_tmap_1(sK6,sK4,sK7,sK8)),
% 0.19/0.55    inference(cnf_transformation,[],[f52])).
% 0.19/0.55  fof(f1024,plain,(
% 0.19/0.55    v1_tsep_1(sK5,sK6) | ~m1_pre_topc(sK5,sK6)),
% 0.19/0.55    inference(subsumption_resolution,[],[f522,f1019])).
% 0.19/0.55  fof(f1019,plain,(
% 0.19/0.55    v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.55    inference(subsumption_resolution,[],[f739,f1013])).
% 0.19/0.55  fof(f1013,plain,(
% 0.19/0.55    v1_tsep_1(sK6,sK6)),
% 0.19/0.55    inference(subsumption_resolution,[],[f801,f1009])).
% 0.19/0.55  fof(f1009,plain,(
% 0.19/0.55    v1_tsep_1(sK5,sK5)),
% 0.19/0.55    inference(subsumption_resolution,[],[f507,f1002])).
% 0.19/0.55  fof(f1002,plain,(
% 0.19/0.55    sP1(sK6)),
% 0.19/0.55    inference(subsumption_resolution,[],[f922,f994])).
% 0.19/0.55  fof(f994,plain,(
% 0.19/0.55    sP1(sK5)),
% 0.19/0.55    inference(subsumption_resolution,[],[f700,f983])).
% 0.19/0.55  fof(f983,plain,(
% 0.19/0.55    sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f982])).
% 0.19/0.55  fof(f982,plain,(
% 0.19/0.55    sP0(sK5) | sP0(sK5)),
% 0.19/0.55    inference(resolution,[],[f981,f102])).
% 0.19/0.55  fof(f102,plain,(
% 0.19/0.55    ( ! [X0] : (r2_hidden(sK11(X0),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f63,plain,(
% 0.19/0.55    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0)) & r2_hidden(sK12(X0),u1_pre_topc(X0)) & r2_hidden(sK11(X0),u1_pre_topc(X0)) & m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f60,f62,f61])).
% 0.19/0.55  fof(f61,plain,(
% 0.19/0.55    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK11(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f62,plain,(
% 0.19/0.55    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK11(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0)) & r2_hidden(sK12(X0),u1_pre_topc(X0)) & r2_hidden(sK11(X0),u1_pre_topc(X0)) & m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f60,plain,(
% 0.19/0.55    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.19/0.55    inference(rectify,[],[f59])).
% 0.19/0.55  fof(f59,plain,(
% 0.19/0.55    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.19/0.55    inference(nnf_transformation,[],[f41])).
% 0.19/0.55  fof(f41,plain,(
% 0.19/0.55    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.55  fof(f981,plain,(
% 0.19/0.55    ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f980])).
% 0.19/0.55  fof(f980,plain,(
% 0.19/0.55    ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5) | sP0(sK5)),
% 0.19/0.55    inference(resolution,[],[f979,f103])).
% 0.19/0.55  fof(f103,plain,(
% 0.19/0.55    ( ! [X0] : (r2_hidden(sK12(X0),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f979,plain,(
% 0.19/0.55    ~r2_hidden(sK12(sK5),u1_pre_topc(sK5)) | ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f978])).
% 0.19/0.55  fof(f978,plain,(
% 0.19/0.55    ~r2_hidden(sK12(sK5),u1_pre_topc(sK5)) | ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5) | sP0(sK5)),
% 0.19/0.55    inference(resolution,[],[f977,f100])).
% 0.19/0.55  fof(f100,plain,(
% 0.19/0.55    ( ! [X0] : (m1_subset_1(sK11(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f977,plain,(
% 0.19/0.55    ~m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK12(sK5),u1_pre_topc(sK5)) | ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f976])).
% 0.19/0.55  fof(f976,plain,(
% 0.19/0.55    ~r2_hidden(sK12(sK5),u1_pre_topc(sK5)) | ~m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5) | sP0(sK5)),
% 0.19/0.55    inference(resolution,[],[f917,f101])).
% 0.19/0.55  fof(f101,plain,(
% 0.19/0.55    ( ! [X0] : (m1_subset_1(sK12(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f917,plain,(
% 0.19/0.55    ~m1_subset_1(sK12(sK5),k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK12(sK5),u1_pre_topc(sK5)) | ~m1_subset_1(sK11(sK5),k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK11(sK5),u1_pre_topc(sK5)) | sP0(sK5)),
% 0.19/0.55    inference(resolution,[],[f915,f104])).
% 0.19/0.55  fof(f104,plain,(
% 0.19/0.55    ( ! [X0] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK11(X0),sK12(X0)),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f915,plain,(
% 0.19/0.55    ( ! [X2,X3] : (r2_hidden(k9_subset_1(u1_struct_0(sK5),X3,X2),u1_pre_topc(sK5)) | ~r2_hidden(X2,u1_pre_topc(sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(X3,u1_pre_topc(sK5))) )),
% 0.19/0.55    inference(global_subsumption,[],[f144,f158,f914])).
% 0.19/0.55  fof(f914,plain,(
% 0.19/0.55    ( ! [X2,X3] : (~r2_hidden(X2,u1_pre_topc(sK5)) | r2_hidden(k9_subset_1(u1_struct_0(sK5),X3,X2),u1_pre_topc(sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(X3,u1_pre_topc(sK5)) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6)) )),
% 0.19/0.55    inference(resolution,[],[f890,f138])).
% 0.19/0.55  fof(f138,plain,(
% 0.19/0.55    ( ! [X0] : (sP0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.55    inference(resolution,[],[f136,f95])).
% 0.19/0.55  fof(f95,plain,(
% 0.19/0.55    ( ! [X0] : (~sP1(X0) | sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f58])).
% 0.19/0.55  fof(f58,plain,(
% 0.19/0.55    ! [X0] : ((sP1(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f57])).
% 0.19/0.55  fof(f57,plain,(
% 0.19/0.55    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) & r1_tarski(sK10(X0),u1_pre_topc(X0)) & m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f56,plain,(
% 0.19/0.55    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.19/0.55    inference(rectify,[],[f55])).
% 0.19/0.55  fof(f55,plain,(
% 0.19/0.55    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.19/0.55    inference(flattening,[],[f54])).
% 0.19/0.55  fof(f54,plain,(
% 0.19/0.55    ! [X0] : ((sP1(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.19/0.55    inference(nnf_transformation,[],[f42])).
% 0.19/0.55  fof(f42,plain,(
% 0.19/0.55    ! [X0] : (sP1(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.19/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.55  fof(f136,plain,(
% 0.19/0.55    ( ! [X0] : (sP1(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(resolution,[],[f91,f105])).
% 0.19/0.55  fof(f105,plain,(
% 0.19/0.55    ( ! [X0] : (sP2(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f44])).
% 0.19/0.55  fof(f44,plain,(
% 0.19/0.55    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(definition_folding,[],[f25,f43,f42,f41])).
% 0.19/0.55  fof(f43,plain,(
% 0.19/0.55    ! [X0] : ((v2_pre_topc(X0) <=> sP1(X0)) | ~sP2(X0))),
% 0.19/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.55  fof(f25,plain,(
% 0.19/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f24])).
% 0.19/0.55  fof(f24,plain,(
% 0.19/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f17])).
% 0.19/0.55  fof(f17,plain,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.19/0.55    inference(rectify,[],[f3])).
% 0.19/0.55  fof(f3,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.19/0.55  fof(f91,plain,(
% 0.19/0.55    ( ! [X0] : (~sP2(X0) | ~v2_pre_topc(X0) | sP1(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f53])).
% 0.19/0.55  fof(f53,plain,(
% 0.19/0.55    ! [X0] : (((v2_pre_topc(X0) | ~sP1(X0)) & (sP1(X0) | ~v2_pre_topc(X0))) | ~sP2(X0))),
% 0.19/0.55    inference(nnf_transformation,[],[f43])).
% 0.19/0.55  fof(f890,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~sP0(sK6) | ~r2_hidden(X1,u1_pre_topc(sK5)) | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(X0,u1_pre_topc(sK5))) )),
% 0.19/0.55    inference(forward_demodulation,[],[f889,f461])).
% 0.19/0.55  fof(f461,plain,(
% 0.19/0.55    u1_pre_topc(sK5) = u1_pre_topc(sK6)),
% 0.19/0.55    inference(trivial_inequality_removal,[],[f459])).
% 0.19/0.55  fof(f459,plain,(
% 0.19/0.55    sK6 != sK6 | u1_pre_topc(sK5) = u1_pre_topc(sK6)),
% 0.19/0.55    inference(superposition,[],[f458,f82])).
% 0.19/0.55  fof(f458,plain,(
% 0.19/0.55    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != sK6 | u1_pre_topc(sK6) = X3) )),
% 0.19/0.55    inference(global_subsumption,[],[f365,f454])).
% 0.19/0.55  fof(f454,plain,(
% 0.19/0.55    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != sK6 | u1_pre_topc(sK6) = X3 | ~m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))) )),
% 0.19/0.55    inference(superposition,[],[f122,f336])).
% 0.19/0.55  fof(f336,plain,(
% 0.19/0.55    sK6 = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK6))),
% 0.19/0.55    inference(backward_demodulation,[],[f173,f332])).
% 0.19/0.55  fof(f122,plain,(
% 0.19/0.55    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.55    inference(cnf_transformation,[],[f40])).
% 0.19/0.55  % (20888)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.55  fof(f365,plain,(
% 0.19/0.55    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.19/0.55    inference(global_subsumption,[],[f144,f344])).
% 0.19/0.55  fof(f344,plain,(
% 0.19/0.55    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~l1_pre_topc(sK6)),
% 0.19/0.55    inference(superposition,[],[f89,f332])).
% 0.19/0.55  fof(f889,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(sK5)) | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) | ~r2_hidden(X0,u1_pre_topc(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~sP0(sK6)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f888,f461])).
% 0.19/0.55  fof(f888,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) | ~r2_hidden(X1,u1_pre_topc(sK6)) | ~r2_hidden(X0,u1_pre_topc(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~sP0(sK6)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f885,f461])).
% 0.19/0.55  fof(f885,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK6)) | ~r2_hidden(X1,u1_pre_topc(sK6)) | ~r2_hidden(X0,u1_pre_topc(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~sP0(sK6)) )),
% 0.19/0.55    inference(superposition,[],[f99,f332])).
% 0.19/0.55  fof(f99,plain,(
% 0.19/0.55    ( ! [X4,X0,X3] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f63])).
% 0.19/0.55  fof(f700,plain,(
% 0.19/0.55    sP1(sK5) | ~sP0(sK5)),
% 0.19/0.55    inference(global_subsumption,[],[f144,f158,f699])).
% 0.19/0.55  fof(f699,plain,(
% 0.19/0.55    sP1(sK5) | ~sP0(sK5) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK6)),
% 0.19/0.55    inference(resolution,[],[f697,f136])).
% 0.19/0.55  fof(f697,plain,(
% 0.19/0.55    ~sP1(sK6) | sP1(sK5) | ~sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f690])).
% 0.19/0.55  fof(f690,plain,(
% 0.19/0.55    sP1(sK5) | ~sP1(sK6) | ~sP0(sK5) | ~sP1(sK6)),
% 0.19/0.55    inference(resolution,[],[f688,f469])).
% 0.19/0.55  fof(f469,plain,(
% 0.19/0.55    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP1(sK6)),
% 0.19/0.55    inference(backward_demodulation,[],[f345,f461])).
% 0.19/0.55  fof(f345,plain,(
% 0.19/0.55    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | ~sP1(sK6)),
% 0.19/0.55    inference(superposition,[],[f93,f332])).
% 0.19/0.55  fof(f93,plain,(
% 0.19/0.55    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP1(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f58])).
% 0.19/0.55  fof(f688,plain,(
% 0.19/0.55    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | sP1(sK5) | ~sP1(sK6) | ~sP0(sK5)),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f687])).
% 0.19/0.55  fof(f687,plain,(
% 0.19/0.55    ~sP0(sK5) | sP1(sK5) | ~sP1(sK6) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK5) | sP1(sK5) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))),
% 0.19/0.55    inference(resolution,[],[f686,f97])).
% 0.19/0.56  fof(f97,plain,(
% 0.19/0.56    ( ! [X0] : (r1_tarski(sK10(X0),u1_pre_topc(X0)) | ~sP0(X0) | sP1(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f58])).
% 0.19/0.56  fof(f686,plain,(
% 0.19/0.56    ~r1_tarski(sK10(sK5),u1_pre_topc(sK5)) | ~sP0(sK5) | sP1(sK5) | ~sP1(sK6) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))),
% 0.19/0.56    inference(duplicate_literal_removal,[],[f685])).
% 0.19/0.56  fof(f685,plain,(
% 0.19/0.56    ~r1_tarski(sK10(sK5),u1_pre_topc(sK5)) | ~sP0(sK5) | sP1(sK5) | ~sP1(sK6) | ~sP0(sK5) | sP1(sK5) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))),
% 0.19/0.56    inference(resolution,[],[f667,f96])).
% 0.19/0.56  fof(f96,plain,(
% 0.19/0.56    ( ! [X0] : (m1_subset_1(sK10(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0) | sP1(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f58])).
% 0.19/0.56  fof(f667,plain,(
% 0.19/0.56    ~m1_subset_1(sK10(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~r1_tarski(sK10(sK5),u1_pre_topc(sK5)) | ~sP0(sK5) | sP1(sK5) | ~sP1(sK6)),
% 0.19/0.56    inference(resolution,[],[f664,f633])).
% 0.19/0.56  fof(f633,plain,(
% 0.19/0.56    ~r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK5)),u1_pre_topc(sK5)) | ~sP0(sK5) | sP1(sK5) | ~sP1(sK6)),
% 0.19/0.56    inference(resolution,[],[f98,f469])).
% 0.19/0.56  fof(f98,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP0(X0) | ~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK10(X0)),u1_pre_topc(X0)) | sP1(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f58])).
% 0.19/0.56  fof(f664,plain,(
% 0.19/0.56    ( ! [X1] : (r2_hidden(k5_setfam_1(u1_struct_0(sK5),X1),u1_pre_topc(sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~r1_tarski(X1,u1_pre_topc(sK5))) )),
% 0.19/0.56    inference(global_subsumption,[],[f144,f158,f663])).
% 0.19/0.56  fof(f663,plain,(
% 0.19/0.56    ( ! [X1] : (r2_hidden(k5_setfam_1(u1_struct_0(sK5),X1),u1_pre_topc(sK5)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~r1_tarski(X1,u1_pre_topc(sK5)) | ~v2_pre_topc(sK6) | ~l1_pre_topc(sK6)) )),
% 0.19/0.56    inference(resolution,[],[f657,f136])).
% 0.19/0.56  fof(f657,plain,(
% 0.19/0.56    ( ! [X0] : (~sP1(sK6) | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~r1_tarski(X0,u1_pre_topc(sK5))) )),
% 0.19/0.56    inference(forward_demodulation,[],[f656,f461])).
% 0.19/0.56  fof(f656,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) | ~r1_tarski(X0,u1_pre_topc(sK6)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~sP1(sK6)) )),
% 0.19/0.56    inference(forward_demodulation,[],[f653,f461])).
% 0.19/0.56  fof(f653,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK6)) | ~r1_tarski(X0,u1_pre_topc(sK6)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~sP1(sK6)) )),
% 0.19/0.56    inference(superposition,[],[f94,f332])).
% 0.19/0.56  fof(f94,plain,(
% 0.19/0.56    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f58])).
% 0.19/0.56  fof(f922,plain,(
% 0.19/0.56    sP1(sK6) | ~sP1(sK5)),
% 0.19/0.56    inference(subsumption_resolution,[],[f655,f918])).
% 0.19/0.56  % (20882)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.56  fof(f918,plain,(
% 0.19/0.56    sP0(sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f346,f347,f486,f487,f916])).
% 0.19/0.56  fof(f916,plain,(
% 0.19/0.56    ~r2_hidden(sK12(sK6),u1_pre_topc(sK5)) | ~m1_subset_1(sK12(sK6),k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_subset_1(sK11(sK6),k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(sK11(sK6),u1_pre_topc(sK5)) | sP0(sK6)),
% 0.19/0.56    inference(resolution,[],[f915,f470])).
% 0.19/0.56  fof(f470,plain,(
% 0.19/0.56    ~r2_hidden(k9_subset_1(u1_struct_0(sK5),sK11(sK6),sK12(sK6)),u1_pre_topc(sK5)) | sP0(sK6)),
% 0.19/0.56    inference(backward_demodulation,[],[f348,f461])).
% 0.19/0.56  fof(f348,plain,(
% 0.19/0.56    ~r2_hidden(k9_subset_1(u1_struct_0(sK5),sK11(sK6),sK12(sK6)),u1_pre_topc(sK6)) | sP0(sK6)),
% 0.19/0.56    inference(superposition,[],[f104,f332])).
% 0.19/0.56  fof(f487,plain,(
% 0.19/0.56    r2_hidden(sK12(sK6),u1_pre_topc(sK5)) | sP0(sK6)),
% 0.19/0.56    inference(superposition,[],[f103,f461])).
% 0.19/0.56  fof(f486,plain,(
% 0.19/0.56    r2_hidden(sK11(sK6),u1_pre_topc(sK5)) | sP0(sK6)),
% 0.19/0.56    inference(superposition,[],[f102,f461])).
% 0.19/0.56  fof(f347,plain,(
% 0.19/0.56    m1_subset_1(sK12(sK6),k1_zfmisc_1(u1_struct_0(sK5))) | sP0(sK6)),
% 0.19/0.56    inference(superposition,[],[f101,f332])).
% 0.19/0.56  fof(f346,plain,(
% 0.19/0.56    m1_subset_1(sK11(sK6),k1_zfmisc_1(u1_struct_0(sK5))) | sP0(sK6)),
% 0.19/0.56    inference(superposition,[],[f100,f332])).
% 0.19/0.56  fof(f655,plain,(
% 0.19/0.56    sP1(sK6) | ~sP1(sK5) | ~sP0(sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f472,f493,f516,f576,f650])).
% 0.19/0.56  fof(f650,plain,(
% 0.19/0.56    ~r1_tarski(sK10(sK6),u1_pre_topc(sK5)) | ~m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~sP1(sK5) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK6) | sP1(sK6)),
% 0.19/0.56    inference(resolution,[],[f94,f644])).
% 0.19/0.56  fof(f644,plain,(
% 0.19/0.56    ~r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK5)) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK6) | sP1(sK6)),
% 0.19/0.56    inference(forward_demodulation,[],[f643,f461])).
% 0.19/0.56  fof(f643,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK6) | ~r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK6)) | sP1(sK6)),
% 0.19/0.56    inference(forward_demodulation,[],[f639,f461])).
% 0.19/0.56  fof(f639,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | ~sP0(sK6) | ~r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK10(sK6)),u1_pre_topc(sK6)) | sP1(sK6)),
% 0.19/0.56    inference(superposition,[],[f98,f332])).
% 0.19/0.56  fof(f576,plain,(
% 0.19/0.56    m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK6) | sP1(sK6)),
% 0.19/0.56    inference(forward_demodulation,[],[f575,f461])).
% 0.19/0.56  fof(f575,plain,(
% 0.19/0.56    m1_subset_1(sK10(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) | ~sP0(sK6) | sP1(sK6) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6))),
% 0.19/0.56    inference(superposition,[],[f96,f332])).
% 0.19/0.56  fof(f516,plain,(
% 0.19/0.56    v3_pre_topc(u1_struct_0(sK5),sK6) | ~sP1(sK5)),
% 0.19/0.56    inference(resolution,[],[f473,f93])).
% 0.19/0.56  fof(f473,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | v3_pre_topc(u1_struct_0(sK5),sK6)),
% 0.19/0.56    inference(backward_demodulation,[],[f378,f461])).
% 0.19/0.56  fof(f378,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | v3_pre_topc(u1_struct_0(sK5),sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f149,f364])).
% 0.19/0.56  fof(f364,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | v3_pre_topc(u1_struct_0(sK5),sK6) | ~m1_pre_topc(sK6,sK6)),
% 0.19/0.56    inference(superposition,[],[f306,f332])).
% 0.19/0.56  fof(f306,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6)) | v3_pre_topc(u1_struct_0(X0),sK6) | ~m1_pre_topc(X0,sK6)) )),
% 0.19/0.56    inference(global_subsumption,[],[f144,f303])).
% 0.19/0.56  fof(f303,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6)) | v3_pre_topc(u1_struct_0(X0),sK6) | ~m1_pre_topc(X0,sK6) | ~l1_pre_topc(sK6)) )),
% 0.19/0.56    inference(resolution,[],[f257,f109])).
% 0.19/0.56  fof(f109,plain,(
% 0.19/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f28])).
% 0.19/0.56  fof(f28,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,axiom,(
% 0.19/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.19/0.56  fof(f257,plain,(
% 0.19/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X3,u1_pre_topc(sK6)) | v3_pre_topc(X3,sK6)) )),
% 0.19/0.56    inference(resolution,[],[f111,f144])).
% 0.19/0.56  fof(f111,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f65])).
% 0.19/0.56  fof(f65,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f29])).
% 0.19/0.56  fof(f29,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f4])).
% 0.19/0.56  fof(f4,axiom,(
% 0.19/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.19/0.56  fof(f149,plain,(
% 0.19/0.56    m1_pre_topc(sK6,sK6)),
% 0.19/0.56    inference(resolution,[],[f144,f88])).
% 0.19/0.56  fof(f88,plain,(
% 0.19/0.56    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f20])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f12])).
% 0.19/0.56  fof(f12,axiom,(
% 0.19/0.56    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.19/0.56  fof(f493,plain,(
% 0.19/0.56    r1_tarski(sK10(sK6),u1_pre_topc(sK5)) | ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~sP0(sK6) | sP1(sK6)),
% 0.19/0.56    inference(forward_demodulation,[],[f485,f332])).
% 0.19/0.56  fof(f485,plain,(
% 0.19/0.56    r1_tarski(sK10(sK6),u1_pre_topc(sK5)) | ~sP0(sK6) | sP1(sK6) | ~r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK5))),
% 0.19/0.56    inference(superposition,[],[f97,f461])).
% 0.19/0.56  fof(f472,plain,(
% 0.19/0.56    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~v3_pre_topc(u1_struct_0(sK5),sK6)),
% 0.19/0.56    inference(backward_demodulation,[],[f372,f461])).
% 0.19/0.56  fof(f372,plain,(
% 0.19/0.56    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | ~v3_pre_topc(u1_struct_0(sK5),sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f149,f356])).
% 0.19/0.56  fof(f356,plain,(
% 0.19/0.56    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK6)) | ~v3_pre_topc(u1_struct_0(sK5),sK6) | ~m1_pre_topc(sK6,sK6)),
% 0.19/0.56    inference(superposition,[],[f253,f332])).
% 0.19/0.56  fof(f253,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6)) | ~v3_pre_topc(u1_struct_0(X0),sK6) | ~m1_pre_topc(X0,sK6)) )),
% 0.19/0.56    inference(global_subsumption,[],[f144,f250])).
% 0.19/0.56  fof(f250,plain,(
% 0.19/0.56    ( ! [X0] : (~v3_pre_topc(u1_struct_0(X0),sK6) | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK6)) | ~m1_pre_topc(X0,sK6) | ~l1_pre_topc(sK6)) )),
% 0.19/0.56    inference(resolution,[],[f237,f109])).
% 0.19/0.56  fof(f237,plain,(
% 0.19/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_pre_topc(X3,sK6) | r2_hidden(X3,u1_pre_topc(sK6))) )),
% 0.19/0.56    inference(resolution,[],[f110,f144])).
% 0.19/0.56  fof(f110,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f65])).
% 0.19/0.56  fof(f507,plain,(
% 0.19/0.56    v1_tsep_1(sK5,sK5) | ~sP1(sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f147,f506])).
% 0.19/0.56  fof(f506,plain,(
% 0.19/0.56    ~sP1(sK6) | ~m1_pre_topc(sK5,sK5) | v1_tsep_1(sK5,sK5)),
% 0.19/0.56    inference(resolution,[],[f503,f285])).
% 0.19/0.56  fof(f285,plain,(
% 0.19/0.56    ( ! [X4] : (~v3_pre_topc(u1_struct_0(X4),sK5) | ~m1_pre_topc(X4,sK5) | v1_tsep_1(X4,sK5)) )),
% 0.19/0.56    inference(global_subsumption,[],[f143,f281])).
% 0.19/0.56  fof(f281,plain,(
% 0.19/0.56    ( ! [X4] : (~v3_pre_topc(u1_struct_0(X4),sK5) | ~m1_pre_topc(X4,sK5) | ~l1_pre_topc(sK5) | v1_tsep_1(X4,sK5)) )),
% 0.19/0.56    inference(resolution,[],[f133,f157])).
% 0.19/0.56  fof(f133,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.19/0.56    inference(global_subsumption,[],[f109,f126])).
% 0.19/0.56  fof(f126,plain,(
% 0.19/0.56    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(equality_resolution,[],[f119])).
% 0.19/0.56  fof(f119,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f68])).
% 0.19/0.56  fof(f68,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(flattening,[],[f67])).
% 0.19/0.56  fof(f67,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f39])).
% 0.19/0.56  fof(f39,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(flattening,[],[f38])).
% 0.19/0.56  fof(f38,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f10])).
% 0.19/0.56  fof(f10,axiom,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.19/0.56  fof(f503,plain,(
% 0.19/0.56    v3_pre_topc(u1_struct_0(sK5),sK5) | ~sP1(sK6)),
% 0.19/0.56    inference(resolution,[],[f469,f377])).
% 0.19/0.56  % (20898)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.56  fof(f377,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.56    inference(global_subsumption,[],[f212,f363])).
% 0.19/0.56  fof(f363,plain,(
% 0.19/0.56    ~r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | v3_pre_topc(u1_struct_0(sK5),sK5) | ~m1_pre_topc(sK6,sK5)),
% 0.19/0.56    inference(superposition,[],[f298,f332])).
% 0.19/0.56  fof(f298,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5)) | v3_pre_topc(u1_struct_0(X0),sK5) | ~m1_pre_topc(X0,sK5)) )),
% 0.19/0.56    inference(global_subsumption,[],[f143,f295])).
% 0.19/0.56  fof(f295,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5)) | v3_pre_topc(u1_struct_0(X0),sK5) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 0.19/0.56    inference(resolution,[],[f256,f109])).
% 0.19/0.56  fof(f256,plain,(
% 0.19/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~r2_hidden(X2,u1_pre_topc(sK5)) | v3_pre_topc(X2,sK5)) )),
% 0.19/0.56    inference(resolution,[],[f111,f143])).
% 0.19/0.56  fof(f212,plain,(
% 0.19/0.56    m1_pre_topc(sK6,sK5)),
% 0.19/0.56    inference(global_subsumption,[],[f144,f209])).
% 0.19/0.56  fof(f209,plain,(
% 0.19/0.56    m1_pre_topc(sK6,sK5) | ~l1_pre_topc(sK6)),
% 0.19/0.56    inference(resolution,[],[f203,f149])).
% 0.19/0.56  fof(f203,plain,(
% 0.19/0.56    ( ! [X2] : (~m1_pre_topc(X2,sK6) | m1_pre_topc(X2,sK5) | ~l1_pre_topc(X2)) )),
% 0.19/0.56    inference(forward_demodulation,[],[f201,f82])).
% 0.19/0.56  fof(f201,plain,(
% 0.19/0.56    ( ! [X2] : (~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) | m1_pre_topc(X2,sK5) | ~l1_pre_topc(X2)) )),
% 0.19/0.56    inference(resolution,[],[f107,f143])).
% 0.19/0.56  fof(f107,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f64])).
% 0.19/0.56  fof(f801,plain,(
% 0.19/0.56    v1_tsep_1(sK6,sK6) | ~v1_tsep_1(sK5,sK5)),
% 0.19/0.56    inference(global_subsumption,[],[f147,f795])).
% 0.19/0.56  fof(f795,plain,(
% 0.19/0.56    ~v1_tsep_1(sK5,sK5) | ~m1_pre_topc(sK5,sK5) | v1_tsep_1(sK6,sK6)),
% 0.19/0.56    inference(resolution,[],[f776,f521])).
% 0.19/0.56  fof(f521,plain,(
% 0.19/0.56    ~v3_pre_topc(u1_struct_0(sK5),sK5) | v1_tsep_1(sK6,sK6)),
% 0.19/0.56    inference(resolution,[],[f514,f376])).
% 0.19/0.56  fof(f376,plain,(
% 0.19/0.56    ~v3_pre_topc(u1_struct_0(sK5),sK6) | v1_tsep_1(sK6,sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f149,f362])).
% 0.19/0.56  fof(f362,plain,(
% 0.19/0.56    ~v3_pre_topc(u1_struct_0(sK5),sK6) | ~m1_pre_topc(sK6,sK6) | v1_tsep_1(sK6,sK6)),
% 0.19/0.56    inference(superposition,[],[f286,f332])).
% 0.19/0.56  fof(f286,plain,(
% 0.19/0.56    ( ! [X5] : (~v3_pre_topc(u1_struct_0(X5),sK6) | ~m1_pre_topc(X5,sK6) | v1_tsep_1(X5,sK6)) )),
% 0.19/0.56    inference(global_subsumption,[],[f144,f282])).
% 0.19/0.56  fof(f282,plain,(
% 0.19/0.56    ( ! [X5] : (~v3_pre_topc(u1_struct_0(X5),sK6) | ~m1_pre_topc(X5,sK6) | ~l1_pre_topc(sK6) | v1_tsep_1(X5,sK6)) )),
% 0.19/0.56    inference(resolution,[],[f133,f158])).
% 0.19/0.56  fof(f514,plain,(
% 0.19/0.56    v3_pre_topc(u1_struct_0(sK5),sK6) | ~v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.56    inference(resolution,[],[f473,f371])).
% 0.19/0.56  % (20887)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.56  fof(f371,plain,(
% 0.19/0.56    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.56    inference(global_subsumption,[],[f212,f355])).
% 0.19/0.56  fof(f355,plain,(
% 0.19/0.56    r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) | ~v3_pre_topc(u1_struct_0(sK5),sK5) | ~m1_pre_topc(sK6,sK5)),
% 0.19/0.56    inference(superposition,[],[f249,f332])).
% 0.19/0.56  fof(f249,plain,(
% 0.19/0.56    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5)) | ~v3_pre_topc(u1_struct_0(X0),sK5) | ~m1_pre_topc(X0,sK5)) )),
% 0.19/0.56    inference(global_subsumption,[],[f143,f246])).
% 0.19/0.56  fof(f246,plain,(
% 0.19/0.56    ( ! [X0] : (~v3_pre_topc(u1_struct_0(X0),sK5) | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK5)) | ~m1_pre_topc(X0,sK5) | ~l1_pre_topc(sK5)) )),
% 0.19/0.56    inference(resolution,[],[f236,f109])).
% 0.19/0.56  fof(f236,plain,(
% 0.19/0.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_pre_topc(X2,sK5) | r2_hidden(X2,u1_pre_topc(sK5))) )),
% 0.19/0.56    inference(resolution,[],[f110,f143])).
% 0.19/0.56  fof(f776,plain,(
% 0.19/0.56    ( ! [X4] : (v3_pre_topc(u1_struct_0(X4),sK5) | ~v1_tsep_1(X4,sK5) | ~m1_pre_topc(X4,sK5)) )),
% 0.19/0.56    inference(global_subsumption,[],[f143,f772])).
% 0.19/0.56  fof(f772,plain,(
% 0.19/0.56    ( ! [X4] : (~v1_tsep_1(X4,sK5) | v3_pre_topc(u1_struct_0(X4),sK5) | ~l1_pre_topc(sK5) | ~m1_pre_topc(X4,sK5)) )),
% 0.19/0.56    inference(resolution,[],[f716,f157])).
% 0.19/0.56  fof(f716,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~v1_tsep_1(X0,X1) | v3_pre_topc(u1_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.19/0.56    inference(duplicate_literal_removal,[],[f709])).
% 0.19/0.56  fof(f709,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~v1_tsep_1(X0,X1) | v3_pre_topc(u1_struct_0(X0),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.19/0.56    inference(resolution,[],[f128,f109])).
% 0.19/0.56  fof(f128,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(duplicate_literal_removal,[],[f127])).
% 0.19/0.56  fof(f127,plain,(
% 0.19/0.56    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(equality_resolution,[],[f118])).
% 0.19/0.56  fof(f118,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f68])).
% 0.19/0.56  fof(f739,plain,(
% 0.19/0.56    v3_pre_topc(u1_struct_0(sK5),sK5) | ~v1_tsep_1(sK6,sK6)),
% 0.19/0.56    inference(global_subsumption,[],[f144,f149,f158,f726])).
% 0.19/0.56  fof(f726,plain,(
% 0.19/0.56    ~v1_tsep_1(sK6,sK6) | ~m1_pre_topc(sK6,sK6) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.56    inference(resolution,[],[f717,f509])).
% 0.19/0.56  fof(f509,plain,(
% 0.19/0.56    ~v3_pre_topc(u1_struct_0(sK5),sK6) | v3_pre_topc(u1_struct_0(sK5),sK5)),
% 0.19/0.56    inference(resolution,[],[f472,f377])).
% 0.19/0.56  fof(f717,plain,(
% 0.19/0.56    ( ! [X0] : (v3_pre_topc(u1_struct_0(sK5),X0) | ~v1_tsep_1(sK6,X0) | ~m1_pre_topc(sK6,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(global_subsumption,[],[f350,f713])).
% 0.19/0.56  fof(f713,plain,(
% 0.19/0.56    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK6,X0) | ~v1_tsep_1(sK6,X0) | v3_pre_topc(u1_struct_0(sK5),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(superposition,[],[f128,f332])).
% 0.19/0.56  fof(f350,plain,(
% 0.19/0.56    ( ! [X1] : (m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK6,X1) | ~l1_pre_topc(X1)) )),
% 0.19/0.56    inference(superposition,[],[f109,f332])).
% 0.19/0.56  fof(f522,plain,(
% 0.19/0.56    ~v3_pre_topc(u1_struct_0(sK5),sK5) | ~m1_pre_topc(sK5,sK6) | v1_tsep_1(sK5,sK6)),
% 0.19/0.56    inference(resolution,[],[f514,f286])).
% 0.19/0.56  fof(f75,plain,(
% 0.19/0.56    ~v2_struct_0(sK5)),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  fof(f147,plain,(
% 0.19/0.56    m1_pre_topc(sK5,sK5)),
% 0.19/0.56    inference(resolution,[],[f143,f88])).
% 0.19/0.56  fof(f69,plain,(
% 0.19/0.56    ~v2_struct_0(sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  fof(f70,plain,(
% 0.19/0.56    v2_pre_topc(sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  fof(f71,plain,(
% 0.19/0.56    l1_pre_topc(sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  fof(f78,plain,(
% 0.19/0.56    m1_pre_topc(sK6,sK3)),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  % SZS output end Proof for theBenchmark
% 0.19/0.56  % (20889)------------------------------
% 0.19/0.56  % (20889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (20889)Termination reason: Refutation
% 0.19/0.56  
% 0.19/0.56  % (20889)Memory used [KB]: 7419
% 0.19/0.56  % (20889)Time elapsed: 0.137 s
% 0.19/0.56  % (20889)------------------------------
% 0.19/0.56  % (20889)------------------------------
% 0.19/0.57  % (20874)Success in time 0.216 s
%------------------------------------------------------------------------------
