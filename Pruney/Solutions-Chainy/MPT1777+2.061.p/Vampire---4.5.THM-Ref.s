%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 828 expanded)
%              Number of leaves         :   30 ( 428 expanded)
%              Depth                    :   25
%              Number of atoms          :  924 (12812 expanded)
%              Number of equality atoms :   46 (1650 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7838)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f241,f298,f334,f341,f441,f454])).

fof(f454,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f452,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f51,f50,f49,f48,f47,f46,f45])).

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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

% (7833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f18,conjecture,(
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

fof(f452,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f450,f189])).

fof(f189,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f140,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f140,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f136,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f136,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f450,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f152,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f152,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_9
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f441,plain,
    ( ~ spl7_8
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f439,f175])).

fof(f175,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f174,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f174,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f169,f57])).

fof(f169,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f89,f64])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f439,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f438,f140])).

fof(f438,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(resolution,[],[f427,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f427,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f426,f189])).

fof(f426,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_struct_0(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(superposition,[],[f422,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f422,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f421,f63])).

fof(f421,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | v2_struct_0(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f420,f175])).

fof(f420,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f419,f140])).

fof(f419,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_8
    | spl7_27 ),
    inference(subsumption_resolution,[],[f417,f149])).

fof(f149,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl7_8
  <=> r2_hidden(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f417,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl7_27 ),
    inference(resolution,[],[f215,f333])).

fof(f333,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK3,sK5)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl7_27
  <=> m1_connsp_2(u1_struct_0(sK3),sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f215,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(u1_struct_0(X1),X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X1)
      | ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f213,f183])).

fof(f183,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f92,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(X1))
      | ~ v3_pre_topc(u1_struct_0(X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | m1_connsp_2(u1_struct_0(X1),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f85,f97])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f341,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl7_26 ),
    inference(subsumption_resolution,[],[f339,f139])).

fof(f139,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f135,f57])).

fof(f135,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f339,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_26 ),
    inference(subsumption_resolution,[],[f336,f266])).

fof(f266,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(subsumption_resolution,[],[f265,f140])).

fof(f265,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f188,f78])).

fof(f78,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f186,f139])).

fof(f186,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(superposition,[],[f83,f68])).

fof(f68,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f336,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | spl7_26 ),
    inference(resolution,[],[f330,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f330,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl7_26
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f334,plain,
    ( ~ spl7_26
    | ~ spl7_27
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f326,f239,f332,f329])).

fof(f239,plain,
    ( spl7_15
  <=> ! [X0] :
        ( ~ m1_connsp_2(X0,sK3,sK5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f326,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK3,sK5)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl7_15 ),
    inference(resolution,[],[f240,f97])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_connsp_2(X0,sK3,sK5)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f239])).

fof(f298,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl7_14 ),
    inference(subsumption_resolution,[],[f296,f139])).

fof(f296,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_14 ),
    inference(subsumption_resolution,[],[f295,f237])).

fof(f237,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl7_14
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f295,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f206,f78])).

fof(f206,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | m1_pre_topc(X0,sK3)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f200,f139])).

fof(f200,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f79,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f241,plain,
    ( ~ spl7_14
    | spl7_15 ),
    inference(avatar_split_clause,[],[f234,f239,f236])).

fof(f234,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f233,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f233,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f57])).

fof(f231,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f230,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f59])).

% (7843)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f228,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f227,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f227,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f226,f62])).

fof(f226,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f225,f63])).

fof(f225,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f224,f64])).

fof(f224,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
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
    inference(subsumption_resolution,[],[f223,f65])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f223,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
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
    inference(subsumption_resolution,[],[f222,f66])).

fof(f66,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_pre_topc(sK2,sK3)
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
    inference(subsumption_resolution,[],[f221,f67])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(X0,sK3,sK5)
      | ~ r1_tarski(X0,u1_struct_0(sK2))
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
    inference(subsumption_resolution,[],[f220,f69])).

fof(f69,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f220,plain,(
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
    inference(subsumption_resolution,[],[f219,f96])).

fof(f96,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f70,f71])).

fof(f71,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

% (7845)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f219,plain,(
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
    inference(subsumption_resolution,[],[f218,f73])).

fof(f73,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f218,plain,(
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
    inference(resolution,[],[f93,f95])).

fof(f95,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(backward_demodulation,[],[f72,f71])).

fof(f72,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f153,plain,
    ( spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f143,f151,f148])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f91,f69])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.44  % (7834)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.45  % (7842)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (7837)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (7829)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (7844)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (7830)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (7832)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (7836)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (7830)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (7838)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f153,f241,f298,f334,f341,f441,f454])).
% 0.22/0.52  fof(f454,plain,(
% 0.22/0.52    ~spl7_9),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f453])).
% 0.22/0.52  fof(f453,plain,(
% 0.22/0.52    $false | ~spl7_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f452,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f51,f50,f49,f48,f47,f46,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(sK0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,X4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ? [X5] : (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,X5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ? [X6] : (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f18])).
% 0.22/0.52  % (7833)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  fof(f18,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 0.22/0.52  fof(f452,plain,(
% 0.22/0.52    v2_struct_0(sK3) | ~spl7_9),
% 0.22/0.52    inference(subsumption_resolution,[],[f450,f189])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    l1_struct_0(sK3)),
% 0.22/0.52    inference(resolution,[],[f140,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    l1_pre_topc(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f136,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f81,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.52  fof(f450,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_9),
% 0.22/0.52    inference(resolution,[],[f152,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl7_9 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.52  fof(f441,plain,(
% 0.22/0.52    ~spl7_8 | spl7_27),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f440])).
% 0.22/0.52  fof(f440,plain,(
% 0.22/0.52    $false | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f439,f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    v2_pre_topc(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f169,f57])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f89,f64])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.52  fof(f439,plain,(
% 0.22/0.52    ~v2_pre_topc(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f438,f140])).
% 0.22/0.52  fof(f438,plain,(
% 0.22/0.52    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(resolution,[],[f427,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.22/0.52  fof(f427,plain,(
% 0.22/0.52    ~v3_pre_topc(k2_struct_0(sK3),sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f426,f189])).
% 0.22/0.52  fof(f426,plain,(
% 0.22/0.52    ~v3_pre_topc(k2_struct_0(sK3),sK3) | ~l1_struct_0(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(superposition,[],[f422,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.52  fof(f422,plain,(
% 0.22/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f421,f63])).
% 0.22/0.52  fof(f421,plain,(
% 0.22/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | v2_struct_0(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f420,f175])).
% 0.22/0.52  fof(f420,plain,(
% 0.22/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f419,f140])).
% 0.22/0.52  fof(f419,plain,(
% 0.22/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl7_8 | spl7_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f417,f149])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    r2_hidden(sK5,u1_struct_0(sK3)) | ~spl7_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl7_8 <=> r2_hidden(sK5,u1_struct_0(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f417,plain,(
% 0.22/0.52    ~v3_pre_topc(u1_struct_0(sK3),sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl7_27),
% 0.22/0.52    inference(resolution,[],[f215,f333])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    ~m1_connsp_2(u1_struct_0(sK3),sK3,sK5) | spl7_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    spl7_27 <=> m1_connsp_2(u1_struct_0(sK3),sK3,sK5)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_connsp_2(u1_struct_0(X1),X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X1) | ~r2_hidden(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f213,f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~r2_hidden(X1,X2) | m1_subset_1(X1,X2)) )),
% 0.22/0.52    inference(resolution,[],[f92,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f75,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(X1)) | ~v3_pre_topc(u1_struct_0(X1),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | m1_connsp_2(u1_struct_0(X1),X1,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f85,f97])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_connsp_2(X1,X0,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.22/0.52  fof(f341,plain,(
% 0.22/0.52    spl7_26),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f340])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    $false | spl7_26),
% 0.22/0.52    inference(subsumption_resolution,[],[f339,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    l1_pre_topc(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f57])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f81,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f339,plain,(
% 0.22/0.52    ~l1_pre_topc(sK2) | spl7_26),
% 0.22/0.52    inference(subsumption_resolution,[],[f336,f266])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f265,f140])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK3)),
% 0.22/0.52    inference(resolution,[],[f188,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f186,f139])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 0.22/0.52    inference(superposition,[],[f83,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.52  fof(f336,plain,(
% 0.22/0.52    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | spl7_26),
% 0.22/0.52    inference(resolution,[],[f330,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.52  fof(f330,plain,(
% 0.22/0.52    ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | spl7_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f329])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    spl7_26 <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ~spl7_26 | ~spl7_27 | ~spl7_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f326,f239,f332,f329])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    spl7_15 <=> ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~r1_tarski(X0,u1_struct_0(sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.52  fof(f326,plain,(
% 0.22/0.52    ~m1_connsp_2(u1_struct_0(sK3),sK3,sK5) | ~r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl7_15),
% 0.22/0.52    inference(resolution,[],[f240,f97])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | ~spl7_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f239])).
% 0.22/0.52  fof(f298,plain,(
% 0.22/0.52    spl7_14),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f297])).
% 0.22/0.52  fof(f297,plain,(
% 0.22/0.52    $false | spl7_14),
% 0.22/0.52    inference(subsumption_resolution,[],[f296,f139])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    ~l1_pre_topc(sK2) | spl7_14),
% 0.22/0.52    inference(subsumption_resolution,[],[f295,f237])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    ~m1_pre_topc(sK2,sK3) | spl7_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f236])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    spl7_14 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.52  fof(f295,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f294])).
% 0.22/0.52  fof(f294,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK2)),
% 0.22/0.52    inference(resolution,[],[f206,f78])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK2) | m1_pre_topc(X0,sK3) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f200,f139])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    ( ! [X0] : (m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(superposition,[],[f79,f68])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    ~spl7_14 | spl7_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f234,f239,f236])).
% 0.22/0.52  fof(f234,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f233,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f232,f56])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f231,f57])).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f230,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f230,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f229,f59])).
% 0.22/0.52  % (7843)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    v2_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f228,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f227,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~v2_struct_0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f227,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f226,f62])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f225,f63])).
% 0.22/0.52  fof(f225,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f224,f64])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f223,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    v1_funct_1(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f222,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f221,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f220,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f219,f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f70,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    sK5 = sK6),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  % (7845)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f218,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tmap_1(sK3,sK1,sK4,sK5) | ~m1_connsp_2(X0,sK3,sK5) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f93,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.53    inference(backward_demodulation,[],[f72,f71])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 0.22/0.53    inference(cnf_transformation,[],[f52])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~m1_connsp_2(X5,X3,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~m1_connsp_2(X5,X3,X6) | ~r1_tarski(X5,u1_struct_0(X2)))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & m1_connsp_2(X5,X3,X6) & r1_tarski(X5,u1_struct_0(X2))) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    spl7_8 | spl7_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f143,f151,f148])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK3)) | r2_hidden(sK5,u1_struct_0(sK3))),
% 0.22/0.53    inference(resolution,[],[f91,f69])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (7830)------------------------------
% 0.22/0.53  % (7830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7830)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (7830)Memory used [KB]: 10874
% 0.22/0.53  % (7830)Time elapsed: 0.091 s
% 0.22/0.53  % (7830)------------------------------
% 0.22/0.53  % (7830)------------------------------
% 0.22/0.53  % (7827)Success in time 0.164 s
%------------------------------------------------------------------------------
