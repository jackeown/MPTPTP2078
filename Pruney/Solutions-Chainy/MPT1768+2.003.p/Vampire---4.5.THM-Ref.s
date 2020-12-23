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
% DateTime   : Thu Dec  3 13:18:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  272 (26654 expanded)
%              Number of leaves         :   17 (13729 expanded)
%              Depth                    :   59
%              Number of atoms          : 1829 (451584 expanded)
%              Number of equality atoms :   96 (1842 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1800,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f309,f731,f1788])).

fof(f1788,plain,
    ( ~ spl6_10
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f1787])).

fof(f1787,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1784,f438])).

fof(f438,plain,(
    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f437,f342])).

fof(f342,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f142,f296])).

fof(f296,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(forward_demodulation,[],[f294,f135])).

fof(f135,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f114,f129])).

fof(f129,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f128,f71])).

fof(f71,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X3)
                        & m1_pre_topc(X3,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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
                        ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X3)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
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
                      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X3)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
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
                    ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X3)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                  & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X3)
              & m1_pre_topc(X3,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
                & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,X3)
            & m1_pre_topc(X3,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
              & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,sK3)
          & m1_pre_topc(sK3,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
            & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
            & v1_funct_1(X5) )
        & m1_pre_topc(X4,sK3)
        & m1_pre_topc(sK3,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK4,sK3)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f70,plain,
    ( v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f128,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f127,f72])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f127,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3,X0)
      | m1_pre_topc(sK4,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f49,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f114,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f112,f71])).

fof(f112,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f111,f72])).

fof(f111,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f110,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f109,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f109,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f108,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f107,f50])).

fof(f50,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f93,f51])).

fof(f51,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f294,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f235,f129])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f234,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f234,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f37])).

fof(f233,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f38])).

fof(f232,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f120,f43])).

fof(f120,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(sK2,X6)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,sK2)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f119,f59])).

fof(f119,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f118,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f116,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f94,f51])).

fof(f94,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK2)
      | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK2,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
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

fof(f142,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(resolution,[],[f139,f47])).

fof(f47,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5)) ) ),
    inference(subsumption_resolution,[],[f138,f36])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f37])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f101,f43])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f39])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f52,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f437,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(subsumption_resolution,[],[f410,f355])).

fof(f355,plain,(
    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f354,f36])).

fof(f354,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f353,f37])).

fof(f353,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f352,f38])).

fof(f352,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f351,f39])).

fof(f351,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f350,f40])).

fof(f350,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f349,f41])).

fof(f349,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f348,f43])).

fof(f348,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f347,f47])).

fof(f347,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f346,f50])).

fof(f346,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f345,f51])).

fof(f345,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f343,f52])).

fof(f343,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f63,f296])).

% (5193)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f27])).

fof(f410,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(resolution,[],[f404,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f404,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f150,f296])).

fof(f150,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f146,f47])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f145,f36])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f37])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f38])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f106,f43])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(sK2,X2)
      | ~ m1_pre_topc(X3,X2)
      | m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f105,f39])).

fof(f105,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f104,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f103,f41])).

fof(f103,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f102,f50])).

fof(f102,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK2,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
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

fof(f1784,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f1596,f1777])).

fof(f1777,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1776,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f1776,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1775,f48])).

fof(f1775,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1774,f312])).

fof(f312,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(backward_demodulation,[],[f141,f295])).

fof(f295,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(forward_demodulation,[],[f293,f134])).

fof(f134,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f114,f48])).

fof(f293,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f235,f48])).

fof(f141,plain,(
    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(resolution,[],[f139,f45])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f34])).

% (5206)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f1774,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1773,f310])).

fof(f310,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f248,f295])).

fof(f248,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl6_10
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1773,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1772,f311])).

fof(f311,plain,(
    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f149,f295])).

fof(f149,plain,(
    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f146,f45])).

fof(f1772,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1771,f403])).

fof(f403,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f402,f312])).

fof(f402,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f375,f310])).

fof(f375,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(resolution,[],[f311,f66])).

fof(f1771,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1770,f49])).

fof(f1770,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1769,f1595])).

fof(f1595,plain,
    ( v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f462,f1520])).

fof(f1520,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1519,f473])).

fof(f473,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ spl6_10 ),
    inference(resolution,[],[f393,f49])).

fof(f393,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f392,f44])).

fof(f392,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f391,f77])).

fof(f77,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f76,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f74,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f45,f58])).

fof(f391,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f390,f78])).

fof(f78,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f75,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f54])).

fof(f390,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f389,f39])).

fof(f389,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f388,f40])).

fof(f388,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f387,f41])).

fof(f387,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f386,f312])).

fof(f386,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f372,f310])).

fof(f372,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK3)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f311,f57])).

fof(f1519,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ spl6_10 ),
    inference(resolution,[],[f904,f49])).

fof(f904,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f903,f36])).

fof(f903,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f902,f37])).

fof(f902,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f900,f38])).

fof(f900,plain,
    ( ! [X0] :
        ( k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f399,f45])).

fof(f399,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(sK3,X6)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ m1_pre_topc(X5,sK3)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f398,f59])).

fof(f398,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(sK3,X6)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f397,f39])).

fof(f397,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(sK3,X6)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f396,f40])).

fof(f396,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(sK3,X6)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f395,f41])).

fof(f395,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(sK3,X6)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f394,f312])).

fof(f394,plain,
    ( ! [X6,X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
        | ~ m1_pre_topc(X5,X6)
        | ~ m1_pre_topc(sK3,X6)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | v2_struct_0(X6) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f373,f310])).

fof(f373,plain,(
    ! [X6,X5] :
      ( ~ m1_pre_topc(X5,sK3)
      | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ m1_pre_topc(X5,X6)
      | ~ m1_pre_topc(sK3,X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f311,f55])).

fof(f462,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)))
    | ~ spl6_10 ),
    inference(resolution,[],[f444,f47])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f443,f36])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f442,f37])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f440,f38])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f380,f45])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f379,f39])).

fof(f379,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f378,f40])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f377,f41])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f376,f312])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f370,f310])).

fof(f370,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f311,f62])).

fof(f1769,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f1768,f1593])).

fof(f1593,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f673,f1520])).

fof(f673,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl6_33
  <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1768,plain,
    ( k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f1750,f1594])).

fof(f1594,plain,
    ( m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f493,f1520])).

fof(f493,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl6_10 ),
    inference(resolution,[],[f487,f47])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f486,f36])).

fof(f486,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f485,f37])).

fof(f485,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f483,f38])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f385,f45])).

fof(f385,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X3,X2)
        | m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f384,f39])).

fof(f384,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f383,f40])).

fof(f383,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f382,f41])).

fof(f382,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f381,f312])).

fof(f381,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
        | ~ m1_pre_topc(X3,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f371,f310])).

fof(f371,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(sK3,X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f311,f64])).

fof(f1750,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4))
    | ~ m1_pre_topc(sK4,sK3)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ spl6_10 ),
    inference(superposition,[],[f829,f1592])).

fof(f1592,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f1591,f473])).

fof(f1591,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ spl6_10 ),
    inference(resolution,[],[f907,f49])).

fof(f907,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK3)
        | k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f906,f42])).

fof(f906,plain,
    ( ! [X1] :
        ( k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f905,f71])).

% (5198)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f905,plain,
    ( ! [X1] :
        ( k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f901,f72])).

fof(f901,plain,
    ( ! [X1] :
        ( k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK3)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl6_10 ),
    inference(resolution,[],[f399,f48])).

fof(f829,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f828,f42])).

fof(f828,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f827,f71])).

fof(f827,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f826,f72])).

fof(f826,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f825,f39])).

fof(f825,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f824,f40])).

fof(f824,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f823,f41])).

fof(f823,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f822,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f822,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f821,f129])).

fof(f821,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f820,f50])).

fof(f820,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f819,f51])).

fof(f819,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f817,f52])).

fof(f817,plain,(
    ! [X0,X1] :
      ( k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1)
      | ~ m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1))
      | ~ m1_pre_topc(sK4,X0)
      | ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
      | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f436,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

fof(f436,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4))
      | k2_tmap_1(sK2,sK1,sK5,sK4) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f435,f342])).

fof(f435,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4))
      | k2_tmap_1(sK2,sK1,sK5,sK4) = X7
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(subsumption_resolution,[],[f409,f355])).

fof(f409,plain,(
    ! [X7] :
      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4))
      | k2_tmap_1(sK2,sK1,sK5,sK4) = X7
      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(X7) ) ),
    inference(resolution,[],[f404,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1596,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f341,f1520])).

fof(f341,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f313,f296])).

fof(f313,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(backward_demodulation,[],[f53,f295])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f731,plain,
    ( ~ spl6_10
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f729,f36])).

fof(f729,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f728,f37])).

fof(f728,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f727,f38])).

fof(f727,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f726,f39])).

fof(f726,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f725,f40])).

fof(f725,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f724,f41])).

fof(f724,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f723,f45])).

fof(f723,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f722,f47])).

fof(f722,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f721,f312])).

fof(f721,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_10
    | spl6_33 ),
    inference(subsumption_resolution,[],[f720,f310])).

fof(f720,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_33 ),
    inference(subsumption_resolution,[],[f719,f311])).

fof(f719,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ m1_pre_topc(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_33 ),
    inference(resolution,[],[f674,f63])).

fof(f674,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1))
    | spl6_33 ),
    inference(avatar_component_clause,[],[f672])).

fof(f309,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl6_10 ),
    inference(subsumption_resolution,[],[f307,f36])).

fof(f307,plain,
    ( v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f306,f37])).

fof(f306,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f305,f38])).

fof(f305,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f304,f39])).

fof(f304,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f303,f40])).

fof(f303,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f302,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f301,f43])).

fof(f301,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f300,f45])).

fof(f300,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f299,f50])).

fof(f299,plain,
    ( ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f298,f51])).

fof(f298,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(subsumption_resolution,[],[f297,f52])).

fof(f297,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_10 ),
    inference(resolution,[],[f249,f63])).

fof(f249,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (5192)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.49  % (5200)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.49  % (5208)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (5201)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (5185)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (5204)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (5189)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (5196)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (5191)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (5188)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (5187)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (5202)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (5197)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (5205)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (5186)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (5203)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (5185)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (5194)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.47/0.54  % (5195)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.47/0.54  % (5184)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.47/0.55  % (5199)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f1800,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(avatar_sat_refutation,[],[f309,f731,f1788])).
% 1.47/0.55  fof(f1788,plain,(
% 1.47/0.55    ~spl6_10 | ~spl6_33),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f1787])).
% 1.47/0.55  fof(f1787,plain,(
% 1.47/0.55    $false | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1784,f438])).
% 1.47/0.55  fof(f438,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.47/0.55    inference(subsumption_resolution,[],[f437,f342])).
% 1.47/0.55  fof(f342,plain,(
% 1.47/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.47/0.55    inference(backward_demodulation,[],[f142,f296])).
% 1.47/0.55  fof(f296,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)),
% 1.47/0.55    inference(forward_demodulation,[],[f294,f135])).
% 1.47/0.55  fof(f135,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.47/0.55    inference(resolution,[],[f114,f129])).
% 1.47/0.55  fof(f129,plain,(
% 1.47/0.55    m1_pre_topc(sK4,sK2)),
% 1.47/0.55    inference(subsumption_resolution,[],[f128,f71])).
% 1.47/0.55  fof(f71,plain,(
% 1.47/0.55    v2_pre_topc(sK2)),
% 1.47/0.55    inference(subsumption_resolution,[],[f70,f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    v2_pre_topc(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30,f29,f28])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,X2,X3,X5)),k3_tmap_1(sK0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,X3,X4,k3_tmap_1(sK0,sK1,sK2,X3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,X4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,X5)),k3_tmap_1(sK0,sK1,sK2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f12,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f11])).
% 1.47/0.55  fof(f11,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f10])).
% 1.47/0.55  fof(f10,negated_conjecture,(
% 1.47/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.47/0.55    inference(negated_conjecture,[],[f9])).
% 1.47/0.55  fof(f9,conjecture,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).
% 1.47/0.55  fof(f70,plain,(
% 1.47/0.55    v2_pre_topc(sK2) | ~v2_pre_topc(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f68,f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    l1_pre_topc(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f68,plain,(
% 1.47/0.55    v2_pre_topc(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.47/0.55    inference(resolution,[],[f43,f58])).
% 1.47/0.55  fof(f58,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.47/0.55    inference(flattening,[],[f20])).
% 1.47/0.55  fof(f20,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f2])).
% 1.47/0.55  fof(f2,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    m1_pre_topc(sK2,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f128,plain,(
% 1.47/0.55    m1_pre_topc(sK4,sK2) | ~v2_pre_topc(sK2)),
% 1.47/0.55    inference(subsumption_resolution,[],[f127,f72])).
% 1.47/0.55  fof(f72,plain,(
% 1.47/0.55    l1_pre_topc(sK2)),
% 1.47/0.55    inference(subsumption_resolution,[],[f69,f38])).
% 1.47/0.55  fof(f69,plain,(
% 1.47/0.55    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.47/0.55    inference(resolution,[],[f43,f54])).
% 1.47/0.55  fof(f54,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f13])).
% 1.47/0.55  fof(f13,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.47/0.55  fof(f127,plain,(
% 1.47/0.55    m1_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.47/0.55    inference(resolution,[],[f88,f48])).
% 1.47/0.55  fof(f48,plain,(
% 1.47/0.55    m1_pre_topc(sK3,sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f88,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(sK3,X0) | m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.55    inference(resolution,[],[f49,f59])).
% 1.47/0.55  fof(f59,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.47/0.55    inference(flattening,[],[f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    m1_pre_topc(sK4,sK3)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f114,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f113,f42])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    ~v2_struct_0(sK2)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f113,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f112,f71])).
% 1.47/0.55  fof(f112,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f111,f72])).
% 1.47/0.55  fof(f111,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f110,f39])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ~v2_struct_0(sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f110,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f109,f40])).
% 1.47/0.55  fof(f40,plain,(
% 1.47/0.55    v2_pre_topc(sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f109,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f108,f41])).
% 1.47/0.55  fof(f41,plain,(
% 1.47/0.55    l1_pre_topc(sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f108,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f107,f50])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    v1_funct_1(sK5)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f107,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f93,f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f93,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK1,sK5,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X4)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.55    inference(resolution,[],[f52,f57])).
% 1.47/0.55  fof(f57,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f19])).
% 1.47/0.55  fof(f19,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f18])).
% 1.47/0.55  fof(f18,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f294,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 1.47/0.55    inference(resolution,[],[f235,f129])).
% 1.47/0.55  fof(f235,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f234,f36])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ~v2_struct_0(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f234,plain,(
% 1.47/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f233,f37])).
% 1.47/0.55  fof(f233,plain,(
% 1.47/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f232,f38])).
% 1.47/0.55  fof(f232,plain,(
% 1.47/0.55    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(resolution,[],[f120,f43])).
% 1.47/0.55  fof(f120,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(sK2,X6) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~m1_pre_topc(X5,sK2) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f119,f59])).
% 1.47/0.55  fof(f119,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f118,f39])).
% 1.47/0.55  fof(f118,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f117,f40])).
% 1.47/0.55  fof(f117,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f116,f41])).
% 1.47/0.55  fof(f116,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f115,f50])).
% 1.47/0.55  fof(f115,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f94,f51])).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK2) | k3_tmap_1(X6,sK1,sK2,X5,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X5)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK2,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(resolution,[],[f52,f55])).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f14])).
% 1.47/0.55  fof(f14,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.47/0.55  fof(f142,plain,(
% 1.47/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 1.47/0.55    inference(resolution,[],[f139,f47])).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    m1_pre_topc(sK4,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f139,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f138,f36])).
% 1.47/0.55  fof(f138,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5)) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f137,f37])).
% 1.47/0.55  fof(f137,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f136,f38])).
% 1.47/0.55  fof(f136,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(resolution,[],[f101,f43])).
% 1.47/0.55  fof(f101,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f100,f39])).
% 1.47/0.55  fof(f100,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f99,f40])).
% 1.47/0.55  fof(f99,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f98,f41])).
% 1.47/0.55  fof(f98,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f97,f50])).
% 1.47/0.55  fof(f97,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f91,f51])).
% 1.47/0.55  fof(f91,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK2,X1,sK5)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(resolution,[],[f52,f62])).
% 1.47/0.55  fof(f62,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f27])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f26])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 1.47/0.55  fof(f437,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.47/0.55    inference(subsumption_resolution,[],[f410,f355])).
% 1.47/0.55  fof(f355,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.47/0.55    inference(subsumption_resolution,[],[f354,f36])).
% 1.47/0.55  fof(f354,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f353,f37])).
% 1.47/0.55  fof(f353,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f352,f38])).
% 1.47/0.55  fof(f352,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f351,f39])).
% 1.47/0.55  fof(f351,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f350,f40])).
% 1.47/0.55  fof(f350,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f349,f41])).
% 1.47/0.55  fof(f349,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f348,f43])).
% 1.47/0.55  fof(f348,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f347,f47])).
% 1.47/0.55  fof(f347,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f346,f50])).
% 1.47/0.55  fof(f346,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f345,f51])).
% 1.47/0.55  fof(f345,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f343,f52])).
% 1.47/0.55  fof(f343,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.47/0.55    inference(superposition,[],[f63,f296])).
% 1.47/0.55  % (5193)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.47/0.55  fof(f63,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f27])).
% 1.47/0.55  fof(f410,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.47/0.55    inference(resolution,[],[f404,f66])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.47/0.55    inference(duplicate_literal_removal,[],[f65])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.47/0.55    inference(equality_resolution,[],[f61])).
% 1.47/0.55  fof(f61,plain,(
% 1.47/0.55    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f35])).
% 1.47/0.55  fof(f35,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.55    inference(nnf_transformation,[],[f25])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.47/0.55    inference(flattening,[],[f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.47/0.55    inference(ennf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.47/0.55  fof(f404,plain,(
% 1.47/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.47/0.55    inference(forward_demodulation,[],[f150,f296])).
% 1.47/0.55  fof(f150,plain,(
% 1.47/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 1.47/0.55    inference(resolution,[],[f146,f47])).
% 1.47/0.55  fof(f146,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f145,f36])).
% 1.47/0.55  fof(f145,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f144,f37])).
% 1.47/0.55  fof(f144,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f143,f38])).
% 1.47/0.55  fof(f143,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.47/0.55    inference(resolution,[],[f106,f43])).
% 1.47/0.55  fof(f106,plain,(
% 1.47/0.55    ( ! [X2,X3] : (~m1_pre_topc(sK2,X2) | ~m1_pre_topc(X3,X2) | m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f105,f39])).
% 1.47/0.55  fof(f105,plain,(
% 1.47/0.55    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f104,f40])).
% 1.47/0.55  fof(f104,plain,(
% 1.47/0.55    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f103,f41])).
% 1.47/0.55  fof(f103,plain,(
% 1.47/0.55    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f102,f50])).
% 1.47/0.55  fof(f102,plain,(
% 1.47/0.55    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f92,f51])).
% 1.47/0.55  fof(f92,plain,(
% 1.47/0.55    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK2,X3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK2,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.55    inference(resolution,[],[f52,f64])).
% 1.47/0.55  fof(f64,plain,(
% 1.47/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f27])).
% 1.47/0.55  fof(f1784,plain,(
% 1.47/0.55    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(backward_demodulation,[],[f1596,f1777])).
% 1.47/0.55  fof(f1777,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1776,f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    ~v2_struct_0(sK3)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  fof(f1776,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1775,f48])).
% 1.47/0.55  fof(f1775,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1774,f312])).
% 1.47/0.55  fof(f312,plain,(
% 1.47/0.55    v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))),
% 1.47/0.55    inference(backward_demodulation,[],[f141,f295])).
% 1.47/0.55  fof(f295,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)),
% 1.47/0.55    inference(forward_demodulation,[],[f293,f134])).
% 1.47/0.55  fof(f134,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 1.47/0.55    inference(resolution,[],[f114,f48])).
% 1.47/0.55  fof(f293,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 1.47/0.55    inference(resolution,[],[f235,f48])).
% 1.47/0.55  fof(f141,plain,(
% 1.47/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5))),
% 1.47/0.55    inference(resolution,[],[f139,f45])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    m1_pre_topc(sK3,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f34])).
% 1.47/0.55  % (5206)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.47/0.55  fof(f1774,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1773,f310])).
% 1.47/0.55  fof(f310,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_10),
% 1.47/0.55    inference(backward_demodulation,[],[f248,f295])).
% 1.47/0.55  fof(f248,plain,(
% 1.47/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl6_10),
% 1.47/0.55    inference(avatar_component_clause,[],[f247])).
% 1.47/0.55  fof(f247,plain,(
% 1.47/0.55    spl6_10 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.47/0.55  fof(f1773,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1772,f311])).
% 1.47/0.55  fof(f311,plain,(
% 1.47/0.55    m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.47/0.55    inference(backward_demodulation,[],[f149,f295])).
% 1.47/0.55  fof(f149,plain,(
% 1.47/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 1.47/0.55    inference(resolution,[],[f146,f45])).
% 1.47/0.55  fof(f1772,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1771,f403])).
% 1.47/0.55  fof(f403,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f402,f312])).
% 1.47/0.55  fof(f402,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f375,f310])).
% 1.47/0.55  fof(f375,plain,(
% 1.47/0.55    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3))),
% 1.47/0.55    inference(resolution,[],[f311,f66])).
% 1.47/0.55  fof(f1771,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1770,f49])).
% 1.47/0.55  fof(f1770,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~m1_pre_topc(sK4,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1769,f1595])).
% 1.47/0.55  fof(f1595,plain,(
% 1.47/0.55    v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)) | ~spl6_10),
% 1.47/0.55    inference(backward_demodulation,[],[f462,f1520])).
% 1.47/0.55  fof(f1520,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~spl6_10),
% 1.47/0.55    inference(forward_demodulation,[],[f1519,f473])).
% 1.47/0.55  fof(f473,plain,(
% 1.47/0.55    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f393,f49])).
% 1.47/0.55  fof(f393,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4))) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f392,f44])).
% 1.47/0.55  fof(f392,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f391,f77])).
% 1.47/0.55  fof(f77,plain,(
% 1.47/0.55    v2_pre_topc(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f76,f37])).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    v2_pre_topc(sK3) | ~v2_pre_topc(sK0)),
% 1.47/0.55    inference(subsumption_resolution,[],[f74,f38])).
% 1.47/0.55  fof(f74,plain,(
% 1.47/0.55    v2_pre_topc(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.47/0.55    inference(resolution,[],[f45,f58])).
% 1.47/0.55  fof(f391,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f390,f78])).
% 1.47/0.55  fof(f78,plain,(
% 1.47/0.55    l1_pre_topc(sK3)),
% 1.47/0.55    inference(subsumption_resolution,[],[f75,f38])).
% 1.47/0.55  fof(f75,plain,(
% 1.47/0.55    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.47/0.55    inference(resolution,[],[f45,f54])).
% 1.47/0.55  fof(f390,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f389,f39])).
% 1.47/0.55  fof(f389,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f388,f40])).
% 1.47/0.55  fof(f388,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f387,f41])).
% 1.47/0.55  fof(f387,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f386,f312])).
% 1.47/0.55  fof(f386,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f372,f310])).
% 1.47/0.55  fof(f372,plain,(
% 1.47/0.55    ( ! [X4] : (~m1_pre_topc(X4,sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X4)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.55    inference(resolution,[],[f311,f57])).
% 1.47/0.55  fof(f1519,plain,(
% 1.47/0.55    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f904,f49])).
% 1.47/0.55  fof(f904,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0))) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f903,f36])).
% 1.47/0.55  fof(f903,plain,(
% 1.47/0.55    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f902,f37])).
% 1.47/0.55  fof(f902,plain,(
% 1.47/0.55    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f900,f38])).
% 1.47/0.55  fof(f900,plain,(
% 1.47/0.55    ( ! [X0] : (k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f399,f45])).
% 1.47/0.55  fof(f399,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(sK3,X6) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~m1_pre_topc(X5,sK3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f398,f59])).
% 1.47/0.55  fof(f398,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f397,f39])).
% 1.47/0.55  fof(f397,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f396,f40])).
% 1.47/0.55  fof(f396,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f395,f41])).
% 1.47/0.55  fof(f395,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f394,f312])).
% 1.47/0.55  fof(f394,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f373,f310])).
% 1.47/0.55  fof(f373,plain,(
% 1.47/0.55    ( ! [X6,X5] : (~m1_pre_topc(X5,sK3) | k3_tmap_1(X6,sK1,sK3,X5,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X5)) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X5,X6) | ~m1_pre_topc(sK3,X6) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 1.47/0.55    inference(resolution,[],[f311,f55])).
% 1.47/0.55  fof(f462,plain,(
% 1.47/0.55    v1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f444,f47])).
% 1.47/0.55  fof(f444,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)))) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f443,f36])).
% 1.47/0.55  fof(f443,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f442,f37])).
% 1.47/0.55  fof(f442,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f440,f38])).
% 1.47/0.55  fof(f440,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v1_funct_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f380,f45])).
% 1.47/0.55  fof(f380,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f379,f39])).
% 1.47/0.55  fof(f379,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f378,f40])).
% 1.47/0.55  fof(f378,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f377,f41])).
% 1.47/0.55  fof(f377,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f376,f312])).
% 1.47/0.55  fof(f376,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f370,f310])).
% 1.47/0.55  fof(f370,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(resolution,[],[f311,f62])).
% 1.47/0.55  fof(f1769,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)) | ~m1_pre_topc(sK4,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(subsumption_resolution,[],[f1768,f1593])).
% 1.47/0.55  fof(f1593,plain,(
% 1.47/0.55    v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | (~spl6_10 | ~spl6_33)),
% 1.47/0.55    inference(backward_demodulation,[],[f673,f1520])).
% 1.47/0.55  fof(f673,plain,(
% 1.47/0.55    v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~spl6_33),
% 1.47/0.55    inference(avatar_component_clause,[],[f672])).
% 1.47/0.55  fof(f672,plain,(
% 1.47/0.55    spl6_33 <=> v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.47/0.55  fof(f1768,plain,(
% 1.47/0.55    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)) | ~m1_pre_topc(sK4,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f1750,f1594])).
% 1.47/0.55  fof(f1594,plain,(
% 1.47/0.55    m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~spl6_10),
% 1.47/0.55    inference(backward_demodulation,[],[f493,f1520])).
% 1.47/0.55  fof(f493,plain,(
% 1.47/0.55    m1_subset_1(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~spl6_10),
% 1.47/0.55    inference(resolution,[],[f487,f47])).
% 1.47/0.55  fof(f487,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f486,f36])).
% 1.47/0.55  fof(f486,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.55    inference(subsumption_resolution,[],[f485,f37])).
% 1.47/0.56  fof(f485,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f483,f38])).
% 1.47/0.56  fof(f483,plain,(
% 1.47/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_subset_1(k3_tmap_1(sK0,sK1,sK3,X0,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_10),
% 1.47/0.56    inference(resolution,[],[f385,f45])).
% 1.47/0.56  fof(f385,plain,(
% 1.47/0.56    ( ! [X2,X3] : (~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X3,X2) | m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f384,f39])).
% 1.47/0.56  fof(f384,plain,(
% 1.47/0.56    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f383,f40])).
% 1.47/0.56  fof(f383,plain,(
% 1.47/0.56    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK3,X2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f382,f41])).
% 1.47/0.56  fof(f382,plain,(
% 1.47/0.56    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f381,f312])).
% 1.47/0.56  fof(f381,plain,(
% 1.47/0.56    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f371,f310])).
% 1.47/0.56  fof(f371,plain,(
% 1.47/0.56    ( ! [X2,X3] : (m1_subset_1(k3_tmap_1(X2,sK1,sK3,X3,k2_tmap_1(sK2,sK1,sK5,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(sK3,X2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.47/0.56    inference(resolution,[],[f311,f64])).
% 1.47/0.56  fof(f1750,plain,(
% 1.47/0.56    ~m1_subset_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | k2_tmap_1(sK2,sK1,sK5,sK4) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~v1_funct_2(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)) | ~m1_pre_topc(sK4,sK3) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~spl6_10),
% 1.47/0.56    inference(superposition,[],[f829,f1592])).
% 1.47/0.56  fof(f1592,plain,(
% 1.47/0.56    k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~spl6_10),
% 1.47/0.56    inference(forward_demodulation,[],[f1591,f473])).
% 1.47/0.56  fof(f1591,plain,(
% 1.47/0.56    k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~spl6_10),
% 1.47/0.56    inference(resolution,[],[f907,f49])).
% 1.47/0.56  fof(f907,plain,(
% 1.47/0.56    ( ! [X1] : (~m1_pre_topc(X1,sK3) | k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1))) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f906,f42])).
% 1.47/0.56  fof(f906,plain,(
% 1.47/0.56    ( ! [X1] : (k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | v2_struct_0(sK2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f905,f71])).
% 1.47/0.56  % (5198)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.47/0.56  fof(f905,plain,(
% 1.47/0.56    ( ! [X1] : (k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f901,f72])).
% 1.47/0.56  fof(f901,plain,(
% 1.47/0.56    ( ! [X1] : (k3_tmap_1(sK2,sK1,sK3,X1,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl6_10),
% 1.47/0.56    inference(resolution,[],[f399,f48])).
% 1.47/0.56  fof(f829,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f828,f42])).
% 1.47/0.56  fof(f828,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f827,f71])).
% 1.47/0.56  fof(f827,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f826,f72])).
% 1.47/0.56  fof(f826,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f825,f39])).
% 1.47/0.56  fof(f825,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f824,f40])).
% 1.47/0.56  fof(f824,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f823,f41])).
% 1.47/0.56  fof(f823,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f822,f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ~v2_struct_0(sK4)),
% 1.47/0.56    inference(cnf_transformation,[],[f34])).
% 1.47/0.56  fof(f822,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f821,f129])).
% 1.47/0.56  fof(f821,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f820,f50])).
% 1.47/0.56  fof(f820,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f819,f51])).
% 1.47/0.56  fof(f819,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f817,f52])).
% 1.47/0.56  fof(f817,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tmap_1(sK2,sK1,sK5,sK4) = k3_tmap_1(sK2,sK1,X0,sK4,X1) | ~m1_subset_1(k3_tmap_1(sK2,sK1,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(k3_tmap_1(sK2,sK1,X0,sK4,X1),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k3_tmap_1(sK2,sK1,X0,sK4,X1)) | ~m1_pre_topc(sK4,X0) | ~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),X1,k2_tmap_1(sK2,sK1,sK5,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) | ~v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.47/0.56    inference(resolution,[],[f436,f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.56    inference(flattening,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).
% 1.47/0.56  fof(f436,plain,(
% 1.47/0.56    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4)) | k2_tmap_1(sK2,sK1,sK5,sK4) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f435,f342])).
% 1.47/0.56  fof(f435,plain,(
% 1.47/0.56    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4)) | k2_tmap_1(sK2,sK1,sK5,sK4) = X7 | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 1.47/0.56    inference(subsumption_resolution,[],[f409,f355])).
% 1.47/0.56  fof(f409,plain,(
% 1.47/0.56    ( ! [X7] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),X7,k2_tmap_1(sK2,sK1,sK5,sK4)) | k2_tmap_1(sK2,sK1,sK5,sK4) = X7 | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK4)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_2(X7,u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(X7)) )),
% 1.47/0.56    inference(resolution,[],[f404,f60])).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f35])).
% 1.47/0.56  fof(f1596,plain,(
% 1.47/0.56    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | ~spl6_10),
% 1.47/0.56    inference(backward_demodulation,[],[f341,f1520])).
% 1.47/0.56  fof(f341,plain,(
% 1.47/0.56    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 1.47/0.56    inference(backward_demodulation,[],[f313,f296])).
% 1.47/0.56  fof(f313,plain,(
% 1.47/0.56    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 1.47/0.56    inference(backward_demodulation,[],[f53,f295])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 1.47/0.56    inference(cnf_transformation,[],[f34])).
% 1.47/0.56  fof(f731,plain,(
% 1.47/0.56    ~spl6_10 | spl6_33),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f730])).
% 1.47/0.56  fof(f730,plain,(
% 1.47/0.56    $false | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f729,f36])).
% 1.47/0.56  fof(f729,plain,(
% 1.47/0.56    v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f728,f37])).
% 1.47/0.56  fof(f728,plain,(
% 1.47/0.56    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f727,f38])).
% 1.47/0.56  fof(f727,plain,(
% 1.47/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f726,f39])).
% 1.47/0.56  fof(f726,plain,(
% 1.47/0.56    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f725,f40])).
% 1.47/0.56  fof(f725,plain,(
% 1.47/0.56    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f724,f41])).
% 1.47/0.56  fof(f724,plain,(
% 1.47/0.56    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f723,f45])).
% 1.47/0.56  fof(f723,plain,(
% 1.47/0.56    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f722,f47])).
% 1.47/0.56  fof(f722,plain,(
% 1.47/0.56    ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f721,f312])).
% 1.47/0.56  fof(f721,plain,(
% 1.47/0.56    ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_10 | spl6_33)),
% 1.47/0.56    inference(subsumption_resolution,[],[f720,f310])).
% 1.47/0.56  fof(f720,plain,(
% 1.47/0.56    ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_33),
% 1.47/0.56    inference(subsumption_resolution,[],[f719,f311])).
% 1.47/0.56  fof(f719,plain,(
% 1.47/0.56    ~m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) | ~m1_pre_topc(sK4,sK0) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_33),
% 1.47/0.56    inference(resolution,[],[f674,f63])).
% 1.47/0.56  fof(f674,plain,(
% 1.47/0.56    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),u1_struct_0(sK4),u1_struct_0(sK1)) | spl6_33),
% 1.47/0.56    inference(avatar_component_clause,[],[f672])).
% 1.47/0.56  fof(f309,plain,(
% 1.47/0.56    spl6_10),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f308])).
% 1.47/0.56  fof(f308,plain,(
% 1.47/0.56    $false | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f307,f36])).
% 1.47/0.56  fof(f307,plain,(
% 1.47/0.56    v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f306,f37])).
% 1.47/0.56  fof(f306,plain,(
% 1.47/0.56    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f305,f38])).
% 1.47/0.56  fof(f305,plain,(
% 1.47/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f304,f39])).
% 1.47/0.56  fof(f304,plain,(
% 1.47/0.56    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f303,f40])).
% 1.47/0.56  fof(f303,plain,(
% 1.47/0.56    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f302,f41])).
% 1.47/0.56  fof(f302,plain,(
% 1.47/0.56    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f301,f43])).
% 1.47/0.56  fof(f301,plain,(
% 1.47/0.56    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f300,f45])).
% 1.47/0.56  fof(f300,plain,(
% 1.47/0.56    ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f299,f50])).
% 1.47/0.56  fof(f299,plain,(
% 1.47/0.56    ~v1_funct_1(sK5) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f298,f51])).
% 1.47/0.56  fof(f298,plain,(
% 1.47/0.56    ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f297,f52])).
% 1.47/0.56  fof(f297,plain,(
% 1.47/0.56    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_10),
% 1.47/0.56    inference(resolution,[],[f249,f63])).
% 1.47/0.56  fof(f249,plain,(
% 1.47/0.56    ~v1_funct_2(k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK3),u1_struct_0(sK1)) | spl6_10),
% 1.47/0.56    inference(avatar_component_clause,[],[f247])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (5185)------------------------------
% 1.47/0.56  % (5185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (5185)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (5185)Memory used [KB]: 11513
% 1.47/0.56  % (5185)Time elapsed: 0.111 s
% 1.47/0.56  % (5185)------------------------------
% 1.47/0.56  % (5185)------------------------------
% 1.47/0.56  % (5183)Success in time 0.2 s
%------------------------------------------------------------------------------
