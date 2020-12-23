%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:05 EST 2020

% Result     : Theorem 3.48s
% Output     : Refutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  197 (1569 expanded)
%              Number of leaves         :   28 ( 782 expanded)
%              Depth                    :   34
%              Number of atoms          : 1068 (23275 expanded)
%              Number of equality atoms :   60 (3023 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4960,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f855,f858,f871,f4959])).

fof(f4959,plain,
    ( ~ spl46_11
    | spl46_12
    | ~ spl46_13 ),
    inference(avatar_contradiction_clause,[],[f4958])).

fof(f4958,plain,
    ( $false
    | ~ spl46_11
    | spl46_12
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4957,f2340])).

fof(f2340,plain,
    ( v3_pre_topc(u1_struct_0(sK16),sK17)
    | ~ spl46_11 ),
    inference(forward_demodulation,[],[f2339,f348])).

fof(f348,plain,(
    g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17 ),
    inference(cnf_transformation,[],[f241])).

fof(f241,plain,
    ( ~ r1_tmap_1(sK17,sK15,sK18,sK19)
    & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20)
    & sK19 = sK20
    & m1_subset_1(sK20,u1_struct_0(sK16))
    & m1_subset_1(sK19,u1_struct_0(sK17))
    & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17
    & m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
    & v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
    & v1_funct_1(sK18)
    & m1_pre_topc(sK17,sK14)
    & ~ v2_struct_0(sK17)
    & m1_pre_topc(sK16,sK14)
    & ~ v2_struct_0(sK16)
    & l1_pre_topc(sK15)
    & v2_pre_topc(sK15)
    & ~ v2_struct_0(sK15)
    & l1_pre_topc(sK14)
    & v2_pre_topc(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16,sK17,sK18,sK19,sK20])],[f122,f240,f239,f238,f237,f236,f235,f234])).

fof(f234,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK14,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK14)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK14)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK14)
      & v2_pre_topc(sK14)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f235,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK14,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK14)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK14)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK15,X4,X5)
                          & r1_tmap_1(X2,sK15,k3_tmap_1(sK14,sK15,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK14)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK14)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK15)
      & v2_pre_topc(sK15)
      & ~ v2_struct_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f236,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK15,X4,X5)
                        & r1_tmap_1(X2,sK15,k3_tmap_1(sK14,sK15,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK14)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK14)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK15,X4,X5)
                      & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,X3,sK16,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK16)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK14)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK16,sK14)
      & ~ v2_struct_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f237,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK15,X4,X5)
                    & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,X3,sK16,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK16)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK14)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK17,sK15,X4,X5)
                  & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK16)) )
              & m1_subset_1(X5,u1_struct_0(sK17)) )
          & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
          & v1_funct_2(X4,u1_struct_0(sK17),u1_struct_0(sK15))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK17,sK14)
      & ~ v2_struct_0(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f238,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK17,sK15,X4,X5)
                & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK16)) )
            & m1_subset_1(X5,u1_struct_0(sK17)) )
        & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
        & v1_funct_2(X4,u1_struct_0(sK17),u1_struct_0(sK15))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK17,sK15,sK18,X5)
              & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK16)) )
          & m1_subset_1(X5,u1_struct_0(sK17)) )
      & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17
      & m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      & v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      & v1_funct_1(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f239,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK17,sK15,sK18,X5)
            & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK16)) )
        & m1_subset_1(X5,u1_struct_0(sK17)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK17,sK15,sK18,sK19)
          & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6)
          & sK19 = X6
          & m1_subset_1(X6,u1_struct_0(sK16)) )
      & m1_subset_1(sK19,u1_struct_0(sK17)) ) ),
    introduced(choice_axiom,[])).

fof(f240,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK17,sK15,sK18,sK19)
        & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6)
        & sK19 = X6
        & m1_subset_1(X6,u1_struct_0(sK16)) )
   => ( ~ r1_tmap_1(sK17,sK15,sK18,sK19)
      & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20)
      & sK19 = sK20
      & m1_subset_1(sK20,u1_struct_0(sK16)) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
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
    inference(flattening,[],[f121])).

fof(f121,plain,(
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
    inference(ennf_transformation,[],[f114])).

fof(f114,negated_conjecture,(
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
    inference(negated_conjecture,[],[f113])).

fof(f113,conjecture,(
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

fof(f2339,plain,
    ( v3_pre_topc(u1_struct_0(sK16),g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)))
    | ~ spl46_11 ),
    inference(resolution,[],[f2242,f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP5(X0,X1) ) ) ),
    inference(flattening,[],[f260])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP5(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f2242,plain,
    ( sP5(sK16,u1_struct_0(sK16))
    | ~ spl46_11 ),
    inference(subsumption_resolution,[],[f2241,f1213])).

fof(f1213,plain,(
    v2_pre_topc(sK16) ),
    inference(resolution,[],[f1211,f342])).

fof(f342,plain,(
    m1_pre_topc(sK16,sK14) ),
    inference(cnf_transformation,[],[f241])).

fof(f1211,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK14)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f1209,f337])).

fof(f337,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f241])).

fof(f1209,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK14)
      | ~ l1_pre_topc(sK14)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f433,f336])).

fof(f336,plain,(
    v2_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f241])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f165])).

fof(f165,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f2241,plain,
    ( sP5(sK16,u1_struct_0(sK16))
    | ~ v2_pre_topc(sK16)
    | ~ spl46_11 ),
    inference(subsumption_resolution,[],[f2238,f573])).

fof(f573,plain,(
    l1_pre_topc(sK16) ),
    inference(resolution,[],[f570,f342])).

fof(f570,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK14)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f436,f337])).

fof(f436,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2238,plain,
    ( sP5(sK16,u1_struct_0(sK16))
    | ~ l1_pre_topc(sK16)
    | ~ v2_pre_topc(sK16)
    | ~ spl46_11 ),
    inference(resolution,[],[f2199,f386])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | sP5(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f264])).

fof(f264,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP4(X0,X1)
            | ~ sP5(X0,X1) )
          & ( sP5(X0,X1)
            | ~ sP4(X0,X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
        <=> sP5(X0,X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f134,f217,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f134,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f2199,plain,
    ( sP4(sK16,u1_struct_0(sK16))
    | ~ spl46_11 ),
    inference(subsumption_resolution,[],[f2180,f1169])).

fof(f1169,plain,
    ( m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ spl46_11 ),
    inference(forward_demodulation,[],[f1160,f796])).

fof(f796,plain,(
    u1_struct_0(sK16) = k2_struct_0(sK16) ),
    inference(resolution,[],[f690,f573])).

fof(f690,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f498,f504])).

fof(f504,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f208])).

fof(f208,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f498,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f207])).

fof(f207,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1160,plain,
    ( m1_subset_1(k2_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ spl46_11 ),
    inference(resolution,[],[f497,f849])).

fof(f849,plain,
    ( l1_struct_0(sK16)
    | ~ spl46_11 ),
    inference(avatar_component_clause,[],[f848])).

fof(f848,plain,
    ( spl46_11
  <=> l1_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_11])])).

fof(f497,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f2180,plain,
    ( ~ m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16)))
    | sP4(sK16,u1_struct_0(sK16)) ),
    inference(resolution,[],[f385,f1226])).

fof(f1226,plain,(
    v3_pre_topc(u1_struct_0(sK16),sK16) ),
    inference(forward_demodulation,[],[f1225,f796])).

fof(f1225,plain,(
    v3_pre_topc(k2_struct_0(sK16),sK16) ),
    inference(subsumption_resolution,[],[f1220,f573])).

fof(f1220,plain,
    ( ~ l1_pre_topc(sK16)
    | v3_pre_topc(k2_struct_0(sK16),sK16) ),
    inference(resolution,[],[f1213,f483])).

fof(f483,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f385,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP4(X0,X1) ) ) ),
    inference(flattening,[],[f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f216])).

fof(f4957,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK16),sK17)
    | ~ spl46_11
    | spl46_12
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4952,f1169])).

fof(f4952,plain,
    ( ~ m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ v3_pre_topc(u1_struct_0(sK16),sK17)
    | ~ spl46_11
    | spl46_12
    | ~ spl46_13 ),
    inference(resolution,[],[f4607,f1078])).

fof(f1078,plain,
    ( r2_hidden(sK19,u1_struct_0(sK16))
    | spl46_12 ),
    inference(subsumption_resolution,[],[f1069,f854])).

fof(f854,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK16))
    | spl46_12 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl46_12
  <=> v1_xboole_0(u1_struct_0(sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_12])])).

fof(f1069,plain,
    ( v1_xboole_0(u1_struct_0(sK16))
    | r2_hidden(sK19,u1_struct_0(sK16)) ),
    inference(resolution,[],[f468,f532])).

fof(f532,plain,(
    m1_subset_1(sK19,u1_struct_0(sK16)) ),
    inference(forward_demodulation,[],[f350,f351])).

fof(f351,plain,(
    sK19 = sK20 ),
    inference(cnf_transformation,[],[f241])).

fof(f350,plain,(
    m1_subset_1(sK20,u1_struct_0(sK16)) ),
    inference(cnf_transformation,[],[f241])).

fof(f468,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f4607,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK19,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16)))
        | ~ v3_pre_topc(X0,sK17) )
    | ~ spl46_11
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4554,f453])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f299])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f4554,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16)))
        | ~ r1_tarski(X0,u1_struct_0(sK16))
        | ~ r2_hidden(sK19,X0)
        | ~ v3_pre_topc(X0,sK17) )
    | ~ spl46_11
    | ~ spl46_13 ),
    inference(backward_demodulation,[],[f3754,f4456])).

fof(f4456,plain,
    ( u1_struct_0(sK16) = u1_struct_0(sK17)
    | ~ spl46_11
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f2511,f4454])).

fof(f4454,plain,
    ( r1_tarski(u1_struct_0(sK17),u1_struct_0(sK16))
    | ~ spl46_13 ),
    inference(resolution,[],[f4392,f453])).

fof(f4392,plain,
    ( m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK16)))
    | ~ spl46_13 ),
    inference(resolution,[],[f4383,f384])).

fof(f384,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f263])).

fof(f4383,plain,
    ( sP4(sK16,u1_struct_0(sK17))
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4382,f1213])).

fof(f4382,plain,
    ( sP4(sK16,u1_struct_0(sK17))
    | ~ v2_pre_topc(sK16)
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4380,f573])).

fof(f4380,plain,
    ( sP4(sK16,u1_struct_0(sK17))
    | ~ l1_pre_topc(sK16)
    | ~ v2_pre_topc(sK16)
    | ~ spl46_13 ),
    inference(resolution,[],[f4361,f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | sP4(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f264])).

fof(f4361,plain,
    ( sP5(sK16,u1_struct_0(sK17))
    | ~ spl46_13 ),
    inference(subsumption_resolution,[],[f4351,f1170])).

fof(f1170,plain,
    ( m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17)))
    | ~ spl46_13 ),
    inference(forward_demodulation,[],[f1161,f797])).

fof(f797,plain,(
    u1_struct_0(sK17) = k2_struct_0(sK17) ),
    inference(resolution,[],[f690,f574])).

fof(f574,plain,(
    l1_pre_topc(sK17) ),
    inference(resolution,[],[f570,f344])).

fof(f344,plain,(
    m1_pre_topc(sK17,sK14) ),
    inference(cnf_transformation,[],[f241])).

fof(f1161,plain,
    ( m1_subset_1(k2_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17)))
    | ~ spl46_13 ),
    inference(resolution,[],[f497,f862])).

fof(f862,plain,
    ( l1_struct_0(sK17)
    | ~ spl46_13 ),
    inference(avatar_component_clause,[],[f861])).

fof(f861,plain,
    ( spl46_13
  <=> l1_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_13])])).

fof(f4351,plain,
    ( sP5(sK16,u1_struct_0(sK17))
    | ~ m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17))) ),
    inference(resolution,[],[f2925,f1237])).

fof(f1237,plain,(
    v3_pre_topc(u1_struct_0(sK17),sK17) ),
    inference(forward_demodulation,[],[f1236,f797])).

fof(f1236,plain,(
    v3_pre_topc(k2_struct_0(sK17),sK17) ),
    inference(subsumption_resolution,[],[f1231,f574])).

fof(f1231,plain,
    ( ~ l1_pre_topc(sK17)
    | v3_pre_topc(k2_struct_0(sK17),sK17) ),
    inference(resolution,[],[f1214,f483])).

fof(f1214,plain,(
    v2_pre_topc(sK17) ),
    inference(resolution,[],[f1211,f344])).

fof(f2925,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK17)
      | sP5(sK16,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) ) ),
    inference(superposition,[],[f382,f348])).

fof(f382,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | sP5(X0,X1)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f261])).

fof(f2511,plain,
    ( ~ r1_tarski(u1_struct_0(sK17),u1_struct_0(sK16))
    | u1_struct_0(sK16) = u1_struct_0(sK17)
    | ~ spl46_11 ),
    inference(resolution,[],[f2508,f457])).

fof(f457,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f301])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2508,plain,
    ( r1_tarski(u1_struct_0(sK16),u1_struct_0(sK17))
    | ~ spl46_11 ),
    inference(resolution,[],[f2468,f453])).

fof(f2468,plain,
    ( m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK17)))
    | ~ spl46_11 ),
    inference(resolution,[],[f2466,f2242])).

fof(f2466,plain,(
    ! [X0] :
      ( ~ sP5(sK16,X0)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) ) ),
    inference(superposition,[],[f381,f348])).

fof(f381,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f261])).

fof(f3754,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) ) ),
    inference(subsumption_resolution,[],[f3753,f335])).

fof(f335,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f241])).

fof(f3753,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3752,f336])).

fof(f3752,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3751,f337])).

fof(f3751,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3750,f338])).

fof(f338,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f241])).

fof(f3750,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3749,f339])).

fof(f339,plain,(
    v2_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f241])).

fof(f3749,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3748,f340])).

fof(f340,plain,(
    l1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f241])).

fof(f3748,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3747,f341])).

fof(f341,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f241])).

fof(f3747,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3746,f343])).

fof(f343,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f241])).

fof(f3746,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3745,f344])).

fof(f3745,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3744,f345])).

fof(f345,plain,(
    v1_funct_1(sK18) ),
    inference(cnf_transformation,[],[f241])).

fof(f3744,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3743,f346])).

fof(f346,plain,(
    v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) ),
    inference(cnf_transformation,[],[f241])).

fof(f3743,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3742,f347])).

fof(f347,plain,(
    m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) ),
    inference(cnf_transformation,[],[f241])).

fof(f3742,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3741,f3374])).

fof(f3374,plain,(
    m1_pre_topc(sK16,sK17) ),
    inference(subsumption_resolution,[],[f3373,f574])).

fof(f3373,plain,
    ( m1_pre_topc(sK16,sK17)
    | ~ l1_pre_topc(sK17) ),
    inference(duplicate_literal_removal,[],[f3368])).

fof(f3368,plain,
    ( m1_pre_topc(sK16,sK17)
    | ~ l1_pre_topc(sK17)
    | ~ l1_pre_topc(sK17) ),
    inference(resolution,[],[f3360,f437])).

fof(f437,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f104])).

fof(f104,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f3360,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK17,X0)
      | m1_pre_topc(sK16,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3359,f1214])).

fof(f3359,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK17,X0)
      | m1_pre_topc(sK16,X0)
      | ~ v2_pre_topc(sK17)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3358,f1213])).

fof(f3358,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK17,X0)
      | ~ v2_pre_topc(sK16)
      | m1_pre_topc(sK16,X0)
      | ~ v2_pre_topc(sK17)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3357,f573])).

fof(f3357,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK17,X0)
      | ~ l1_pre_topc(sK16)
      | ~ v2_pre_topc(sK16)
      | m1_pre_topc(sK16,X0)
      | ~ v2_pre_topc(sK17)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f3356,f574])).

fof(f3356,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK17)
      | ~ m1_pre_topc(sK17,X0)
      | ~ l1_pre_topc(sK16)
      | ~ v2_pre_topc(sK16)
      | m1_pre_topc(sK16,X0)
      | ~ v2_pre_topc(sK17)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f517,f348])).

fof(f517,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f396])).

fof(f396,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f270])).

fof(f270,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f102])).

fof(f102,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f3741,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_pre_topc(sK16,sK17)
      | ~ m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3740,f349])).

fof(f349,plain,(
    m1_subset_1(sK19,u1_struct_0(sK17)) ),
    inference(cnf_transformation,[],[f241])).

fof(f3740,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(sK19,u1_struct_0(sK17))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_pre_topc(sK16,sK17)
      | ~ m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3739,f532])).

fof(f3739,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(sK19,u1_struct_0(sK16))
      | ~ m1_subset_1(sK19,u1_struct_0(sK17))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_pre_topc(sK16,sK17)
      | ~ m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f3738,f353])).

fof(f353,plain,(
    ~ r1_tmap_1(sK17,sK15,sK18,sK19) ),
    inference(cnf_transformation,[],[f241])).

fof(f3738,plain,(
    ! [X0] :
      ( r1_tmap_1(sK17,sK15,sK18,sK19)
      | ~ r1_tarski(X0,u1_struct_0(sK16))
      | ~ r2_hidden(sK19,X0)
      | ~ v3_pre_topc(X0,sK17)
      | ~ m1_subset_1(sK19,u1_struct_0(sK16))
      | ~ m1_subset_1(sK19,u1_struct_0(sK17))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))
      | ~ m1_pre_topc(sK16,sK17)
      | ~ m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))
      | ~ v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))
      | ~ v1_funct_1(sK18)
      | ~ m1_pre_topc(sK17,sK14)
      | v2_struct_0(sK17)
      | v2_struct_0(sK16)
      | ~ l1_pre_topc(sK15)
      | ~ v2_pre_topc(sK15)
      | v2_struct_0(sK15)
      | ~ l1_pre_topc(sK14)
      | ~ v2_pre_topc(sK14)
      | v2_struct_0(sK14) ) ),
    inference(resolution,[],[f537,f531])).

fof(f531,plain,(
    r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK19) ),
    inference(backward_demodulation,[],[f352,f351])).

fof(f352,plain,(
    r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20) ),
    inference(cnf_transformation,[],[f241])).

fof(f537,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
      | ~ m1_subset_1(X7,u1_struct_0(X2))
      | ~ m1_subset_1(X7,u1_struct_0(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f510,f432])).

fof(f432,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f163])).

fof(f163,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f162])).

fof(f162,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f109])).

fof(f109,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f510,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f371])).

fof(f371,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f256])).

fof(f256,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f128])).

fof(f128,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f127])).

fof(f127,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f111])).

fof(f111,axiom,(
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
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X3) )
                                     => ( r1_tmap_1(X3,X1,X4,X6)
                                      <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(f871,plain,(
    spl46_13 ),
    inference(avatar_contradiction_clause,[],[f870])).

fof(f870,plain,
    ( $false
    | spl46_13 ),
    inference(subsumption_resolution,[],[f869,f574])).

fof(f869,plain,
    ( ~ l1_pre_topc(sK17)
    | spl46_13 ),
    inference(resolution,[],[f863,f504])).

fof(f863,plain,
    ( ~ l1_struct_0(sK17)
    | spl46_13 ),
    inference(avatar_component_clause,[],[f861])).

fof(f858,plain,(
    spl46_11 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | spl46_11 ),
    inference(subsumption_resolution,[],[f856,f573])).

fof(f856,plain,
    ( ~ l1_pre_topc(sK16)
    | spl46_11 ),
    inference(resolution,[],[f850,f504])).

fof(f850,plain,
    ( ~ l1_struct_0(sK16)
    | spl46_11 ),
    inference(avatar_component_clause,[],[f848])).

fof(f855,plain,
    ( ~ spl46_11
    | ~ spl46_12 ),
    inference(avatar_split_clause,[],[f818,f852,f848])).

fof(f818,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK16))
    | ~ l1_struct_0(sK16) ),
    inference(subsumption_resolution,[],[f817,f341])).

fof(f817,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK16))
    | ~ l1_struct_0(sK16)
    | v2_struct_0(sK16) ),
    inference(superposition,[],[f496,f796])).

fof(f496,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f205])).

fof(f205,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (30708)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_3 on theBenchmark
% 0.22/0.54  % (30710)ott+1010_5:4_av=off:bd=off:fde=none:irw=on:lma=on:nm=32:nwc=2.5:sd=2:ss=axioms:st=3.0:urr=on_5 on theBenchmark
% 1.31/0.54  % (30719)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_5 on theBenchmark
% 1.31/0.55  % (30724)dis+11_3:1_add=off:afr=on:afp=100000:afq=1.2:amm=off:anc=none:bd=off:bs=unit_only:irw=on:lcm=predicate:lma=on:nm=2:nwc=1:sd=2:ss=axioms:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 1.31/0.55  % (30730)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_72 on theBenchmark
% 1.31/0.55  % (30712)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (30722)ott+1_8_av=off:bd=off:bs=on:cond=on:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:lwlo=on:nwc=1:sos=on_10 on theBenchmark
% 1.31/0.55  % (30709)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_2 on theBenchmark
% 1.31/0.55  % (30714)ott+1002_2_av=off:bd=preordered:irw=on:lma=on:nm=64:nwc=10:sp=reverse_arity:updr=off_22 on theBenchmark
% 1.31/0.55  % (30715)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_16 on theBenchmark
% 1.31/0.56  % (30720)lrs+1003_2_acc=on:afp=4000:afq=2.0:amm=sco:bd=off:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:nm=64:newcnf=on:nwc=2.5:nicw=on:stl=30:urr=ec_only_8 on theBenchmark
% 1.31/0.56  % (30737)ott+11_8_amm=off:anc=none:bsr=on:cond=on:irw=on:nm=2:nwc=1.1:ss=axioms:st=2.0:sac=on_1 on theBenchmark
% 1.31/0.56  % (30711)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_3 on theBenchmark
% 1.31/0.56  % (30732)lrs+1011_4:1_av=off:fsr=off:irw=on:nwc=1:stl=30:sd=4:ss=axioms:st=1.5:sp=reverse_arity_12 on theBenchmark
% 1.31/0.56  % (30725)lrs+1002_3_aac=none:acc=on:add=off:afp=4000:afq=1.1:amm=sco:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1.1:nicw=on:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=occurrence:updr=off_24 on theBenchmark
% 1.31/0.56  % (30729)dis+11_28_av=off:fsr=off:irw=on:lcm=predicate:nm=2:newcnf=on:nwc=5:sp=occurrence:urr=on:updr=off_2 on theBenchmark
% 1.31/0.56  % (30734)ott+1002_128_av=off:bd=off:bs=on:bsr=on:cond=on:fsr=off:nm=6:newcnf=on:nwc=1:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.57  % (30716)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.57  % (30713)dis+1011_10_aac=none:add=large:afp=10000:afq=1.1:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=6:newcnf=on:nwc=2.5:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.57  % (30731)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.31/0.57  % (30723)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_4 on theBenchmark
% 1.59/0.57  % (30717)dis+11_4_afr=on:afp=1000:afq=1.4:amm=off:anc=none:lcm=reverse:lma=on:lwlo=on:nm=6:newcnf=on:nwc=1:sd=2:ss=axioms:st=2.0:sp=reverse_arity_2 on theBenchmark
% 1.59/0.57  % (30726)dis+1010_4_afp=10000:afq=1.2:anc=none:irw=on:lma=on:nm=64:nwc=10:sas=z3:sac=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.58  % (30733)dis+11_5_av=off:bd=off:bs=unit_only:bsr=on:cond=on:lcm=reverse:nm=0:nwc=1.2_5 on theBenchmark
% 1.59/0.58  % (30727)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_36 on theBenchmark
% 1.59/0.59  % (30718)dis-3_5_av=off:cond=on:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1:sos=on:sp=reverse_arity_3 on theBenchmark
% 1.59/0.59  % (30735)dis+1003_64_add=off:afr=on:afp=100000:afq=1.1:anc=none:cond=fast:fde=none:irw=on:nm=6:newcnf=on:nwc=1.3:uhcvi=on_5 on theBenchmark
% 1.59/0.59  % (30736)lrs+10_6_aac=none:acc=model:add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bd=off:ccuc=small_ones:irw=on:lcm=reverse:nm=0:nwc=1:nicw=on:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.59  % (30721)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_14 on theBenchmark
% 1.59/0.60  % (30728)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_2 on theBenchmark
% 3.48/0.82  % (30724)Time limit reached!
% 3.48/0.82  % (30724)------------------------------
% 3.48/0.82  % (30724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.82  % (30724)Termination reason: Time limit
% 3.48/0.82  
% 3.48/0.82  % (30724)Memory used [KB]: 8315
% 3.48/0.82  % (30724)Time elapsed: 0.404 s
% 3.48/0.82  % (30724)------------------------------
% 3.48/0.82  % (30724)------------------------------
% 3.48/0.84  % (30737)Refutation found. Thanks to Tanya!
% 3.48/0.84  % SZS status Theorem for theBenchmark
% 3.48/0.84  % SZS output start Proof for theBenchmark
% 3.48/0.84  fof(f4960,plain,(
% 3.48/0.84    $false),
% 3.48/0.84    inference(avatar_sat_refutation,[],[f855,f858,f871,f4959])).
% 3.48/0.84  fof(f4959,plain,(
% 3.48/0.84    ~spl46_11 | spl46_12 | ~spl46_13),
% 3.48/0.84    inference(avatar_contradiction_clause,[],[f4958])).
% 3.48/0.84  fof(f4958,plain,(
% 3.48/0.84    $false | (~spl46_11 | spl46_12 | ~spl46_13)),
% 3.48/0.84    inference(subsumption_resolution,[],[f4957,f2340])).
% 3.48/0.84  fof(f2340,plain,(
% 3.48/0.84    v3_pre_topc(u1_struct_0(sK16),sK17) | ~spl46_11),
% 3.48/0.84    inference(forward_demodulation,[],[f2339,f348])).
% 3.48/0.84  fof(f348,plain,(
% 3.48/0.84    g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f241,plain,(
% 3.48/0.84    ((((((~r1_tmap_1(sK17,sK15,sK18,sK19) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20) & sK19 = sK20 & m1_subset_1(sK20,u1_struct_0(sK16))) & m1_subset_1(sK19,u1_struct_0(sK17))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17 & m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) & v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) & v1_funct_1(sK18)) & m1_pre_topc(sK17,sK14) & ~v2_struct_0(sK17)) & m1_pre_topc(sK16,sK14) & ~v2_struct_0(sK16)) & l1_pre_topc(sK15) & v2_pre_topc(sK15) & ~v2_struct_0(sK15)) & l1_pre_topc(sK14) & v2_pre_topc(sK14) & ~v2_struct_0(sK14)),
% 3.48/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16,sK17,sK18,sK19,sK20])],[f122,f240,f239,f238,f237,f236,f235,f234])).
% 3.48/0.84  fof(f234,plain,(
% 3.48/0.84    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK14,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK14) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK14) & v2_pre_topc(sK14) & ~v2_struct_0(sK14))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f235,plain,(
% 3.48/0.84    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK14,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK14) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK15,X4,X5) & r1_tmap_1(X2,sK15,k3_tmap_1(sK14,sK15,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK14) & ~v2_struct_0(X2)) & l1_pre_topc(sK15) & v2_pre_topc(sK15) & ~v2_struct_0(sK15))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f236,plain,(
% 3.48/0.84    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK15,X4,X5) & r1_tmap_1(X2,sK15,k3_tmap_1(sK14,sK15,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK14) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK15,X4,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,X3,sK16,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) & m1_pre_topc(sK16,sK14) & ~v2_struct_0(sK16))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f237,plain,(
% 3.48/0.84    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK15,X4,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,X3,sK16,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK15)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK14) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK17,sK15,X4,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(sK17))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(sK17),u1_struct_0(sK15)) & v1_funct_1(X4)) & m1_pre_topc(sK17,sK14) & ~v2_struct_0(sK17))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f238,plain,(
% 3.48/0.84    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK17,sK15,X4,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(sK17))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) & v1_funct_2(X4,u1_struct_0(sK17),u1_struct_0(sK15)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK17,sK15,sK18,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(sK17))) & g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16)) = sK17 & m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) & v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) & v1_funct_1(sK18))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f239,plain,(
% 3.48/0.84    ? [X5] : (? [X6] : (~r1_tmap_1(sK17,sK15,sK18,X5) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(X5,u1_struct_0(sK17))) => (? [X6] : (~r1_tmap_1(sK17,sK15,sK18,sK19) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6) & sK19 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) & m1_subset_1(sK19,u1_struct_0(sK17)))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f240,plain,(
% 3.48/0.84    ? [X6] : (~r1_tmap_1(sK17,sK15,sK18,sK19) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),X6) & sK19 = X6 & m1_subset_1(X6,u1_struct_0(sK16))) => (~r1_tmap_1(sK17,sK15,sK18,sK19) & r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20) & sK19 = sK20 & m1_subset_1(sK20,u1_struct_0(sK16)))),
% 3.48/0.84    introduced(choice_axiom,[])).
% 3.48/0.84  fof(f122,plain,(
% 3.48/0.84    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.48/0.84    inference(flattening,[],[f121])).
% 3.48/0.84  fof(f121,plain,(
% 3.48/0.84    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f114])).
% 3.48/0.84  fof(f114,negated_conjecture,(
% 3.48/0.84    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.48/0.84    inference(negated_conjecture,[],[f113])).
% 3.48/0.84  fof(f113,conjecture,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 3.48/0.84  fof(f2339,plain,(
% 3.48/0.84    v3_pre_topc(u1_struct_0(sK16),g1_pre_topc(u1_struct_0(sK16),u1_pre_topc(sK16))) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f2242,f380])).
% 3.48/0.84  fof(f380,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~sP5(X0,X1) | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 3.48/0.84    inference(cnf_transformation,[],[f261])).
% 3.48/0.84  fof(f261,plain,(
% 3.48/0.84    ! [X0,X1] : ((sP5(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP5(X0,X1)))),
% 3.48/0.84    inference(flattening,[],[f260])).
% 3.48/0.84  fof(f260,plain,(
% 3.48/0.84    ! [X0,X1] : ((sP5(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP5(X0,X1)))),
% 3.48/0.84    inference(nnf_transformation,[],[f217])).
% 3.48/0.84  fof(f217,plain,(
% 3.48/0.84    ! [X0,X1] : (sP5(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.48/0.84    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 3.48/0.84  fof(f2242,plain,(
% 3.48/0.84    sP5(sK16,u1_struct_0(sK16)) | ~spl46_11),
% 3.48/0.84    inference(subsumption_resolution,[],[f2241,f1213])).
% 3.48/0.84  fof(f1213,plain,(
% 3.48/0.84    v2_pre_topc(sK16)),
% 3.48/0.84    inference(resolution,[],[f1211,f342])).
% 3.48/0.84  fof(f342,plain,(
% 3.48/0.84    m1_pre_topc(sK16,sK14)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f1211,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK14) | v2_pre_topc(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f1209,f337])).
% 3.48/0.84  fof(f337,plain,(
% 3.48/0.84    l1_pre_topc(sK14)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f1209,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK14) | ~l1_pre_topc(sK14) | v2_pre_topc(X0)) )),
% 3.48/0.84    inference(resolution,[],[f433,f336])).
% 3.48/0.84  fof(f336,plain,(
% 3.48/0.84    v2_pre_topc(sK14)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f433,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f165])).
% 3.48/0.84  fof(f165,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(flattening,[],[f164])).
% 3.48/0.84  fof(f164,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f58])).
% 3.48/0.84  fof(f58,axiom,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 3.48/0.84  fof(f2241,plain,(
% 3.48/0.84    sP5(sK16,u1_struct_0(sK16)) | ~v2_pre_topc(sK16) | ~spl46_11),
% 3.48/0.84    inference(subsumption_resolution,[],[f2238,f573])).
% 3.48/0.84  fof(f573,plain,(
% 3.48/0.84    l1_pre_topc(sK16)),
% 3.48/0.84    inference(resolution,[],[f570,f342])).
% 3.48/0.84  fof(f570,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(X0,sK14) | l1_pre_topc(X0)) )),
% 3.48/0.84    inference(resolution,[],[f436,f337])).
% 3.48/0.84  fof(f436,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f168])).
% 3.48/0.84  fof(f168,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f63])).
% 3.48/0.84  fof(f63,axiom,(
% 3.48/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 3.48/0.84  fof(f2238,plain,(
% 3.48/0.84    sP5(sK16,u1_struct_0(sK16)) | ~l1_pre_topc(sK16) | ~v2_pre_topc(sK16) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f2199,f386])).
% 3.48/0.84  fof(f386,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~sP4(X0,X1) | sP5(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f264])).
% 3.48/0.84  fof(f264,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : ((sP4(X0,X1) | ~sP5(X0,X1)) & (sP5(X0,X1) | ~sP4(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(nnf_transformation,[],[f218])).
% 3.48/0.84  fof(f218,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (sP4(X0,X1) <=> sP5(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(definition_folding,[],[f134,f217,f216])).
% 3.48/0.84  fof(f216,plain,(
% 3.48/0.84    ! [X0,X1] : (sP4(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))),
% 3.48/0.84    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.48/0.84  fof(f134,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(flattening,[],[f133])).
% 3.48/0.84  fof(f133,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f79])).
% 3.48/0.84  fof(f79,axiom,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).
% 3.48/0.84  fof(f2199,plain,(
% 3.48/0.84    sP4(sK16,u1_struct_0(sK16)) | ~spl46_11),
% 3.48/0.84    inference(subsumption_resolution,[],[f2180,f1169])).
% 3.48/0.84  fof(f1169,plain,(
% 3.48/0.84    m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16))) | ~spl46_11),
% 3.48/0.84    inference(forward_demodulation,[],[f1160,f796])).
% 3.48/0.84  fof(f796,plain,(
% 3.48/0.84    u1_struct_0(sK16) = k2_struct_0(sK16)),
% 3.48/0.84    inference(resolution,[],[f690,f573])).
% 3.48/0.84  fof(f690,plain,(
% 3.48/0.84    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 3.48/0.84    inference(resolution,[],[f498,f504])).
% 3.48/0.84  fof(f504,plain,(
% 3.48/0.84    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f208])).
% 3.48/0.84  fof(f208,plain,(
% 3.48/0.84    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f62])).
% 3.48/0.84  fof(f62,axiom,(
% 3.48/0.84    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.48/0.84  fof(f498,plain,(
% 3.48/0.84    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f207])).
% 3.48/0.84  fof(f207,plain,(
% 3.48/0.84    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f60])).
% 3.48/0.84  fof(f60,axiom,(
% 3.48/0.84    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.48/0.84  fof(f1160,plain,(
% 3.48/0.84    m1_subset_1(k2_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16))) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f497,f849])).
% 3.48/0.84  fof(f849,plain,(
% 3.48/0.84    l1_struct_0(sK16) | ~spl46_11),
% 3.48/0.84    inference(avatar_component_clause,[],[f848])).
% 3.48/0.84  fof(f848,plain,(
% 3.48/0.84    spl46_11 <=> l1_struct_0(sK16)),
% 3.48/0.84    introduced(avatar_definition,[new_symbols(naming,[spl46_11])])).
% 3.48/0.84  fof(f497,plain,(
% 3.48/0.84    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.48/0.84    inference(cnf_transformation,[],[f206])).
% 3.48/0.84  fof(f206,plain,(
% 3.48/0.84    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f61])).
% 3.48/0.84  fof(f61,axiom,(
% 3.48/0.84    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 3.48/0.84  fof(f2180,plain,(
% 3.48/0.84    ~m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16))) | sP4(sK16,u1_struct_0(sK16))),
% 3.48/0.84    inference(resolution,[],[f385,f1226])).
% 3.48/0.84  fof(f1226,plain,(
% 3.48/0.84    v3_pre_topc(u1_struct_0(sK16),sK16)),
% 3.48/0.84    inference(forward_demodulation,[],[f1225,f796])).
% 3.48/0.84  fof(f1225,plain,(
% 3.48/0.84    v3_pre_topc(k2_struct_0(sK16),sK16)),
% 3.48/0.84    inference(subsumption_resolution,[],[f1220,f573])).
% 3.48/0.84  fof(f1220,plain,(
% 3.48/0.84    ~l1_pre_topc(sK16) | v3_pre_topc(k2_struct_0(sK16),sK16)),
% 3.48/0.84    inference(resolution,[],[f1213,f483])).
% 3.48/0.84  fof(f483,plain,(
% 3.48/0.84    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f196])).
% 3.48/0.84  fof(f196,plain,(
% 3.48/0.84    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(flattening,[],[f195])).
% 3.48/0.84  fof(f195,plain,(
% 3.48/0.84    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f90])).
% 3.48/0.84  fof(f90,axiom,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 3.48/0.84  fof(f385,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP4(X0,X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f263])).
% 3.48/0.84  fof(f263,plain,(
% 3.48/0.84    ! [X0,X1] : ((sP4(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP4(X0,X1)))),
% 3.48/0.84    inference(flattening,[],[f262])).
% 3.48/0.84  fof(f262,plain,(
% 3.48/0.84    ! [X0,X1] : ((sP4(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP4(X0,X1)))),
% 3.48/0.84    inference(nnf_transformation,[],[f216])).
% 3.48/0.84  fof(f4957,plain,(
% 3.48/0.84    ~v3_pre_topc(u1_struct_0(sK16),sK17) | (~spl46_11 | spl46_12 | ~spl46_13)),
% 3.48/0.84    inference(subsumption_resolution,[],[f4952,f1169])).
% 3.48/0.84  fof(f4952,plain,(
% 3.48/0.84    ~m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK16))) | ~v3_pre_topc(u1_struct_0(sK16),sK17) | (~spl46_11 | spl46_12 | ~spl46_13)),
% 3.48/0.84    inference(resolution,[],[f4607,f1078])).
% 3.48/0.84  fof(f1078,plain,(
% 3.48/0.84    r2_hidden(sK19,u1_struct_0(sK16)) | spl46_12),
% 3.48/0.84    inference(subsumption_resolution,[],[f1069,f854])).
% 3.48/0.84  fof(f854,plain,(
% 3.48/0.84    ~v1_xboole_0(u1_struct_0(sK16)) | spl46_12),
% 3.48/0.84    inference(avatar_component_clause,[],[f852])).
% 3.48/0.84  fof(f852,plain,(
% 3.48/0.84    spl46_12 <=> v1_xboole_0(u1_struct_0(sK16))),
% 3.48/0.84    introduced(avatar_definition,[new_symbols(naming,[spl46_12])])).
% 3.48/0.84  fof(f1069,plain,(
% 3.48/0.84    v1_xboole_0(u1_struct_0(sK16)) | r2_hidden(sK19,u1_struct_0(sK16))),
% 3.48/0.84    inference(resolution,[],[f468,f532])).
% 3.48/0.84  fof(f532,plain,(
% 3.48/0.84    m1_subset_1(sK19,u1_struct_0(sK16))),
% 3.48/0.84    inference(forward_demodulation,[],[f350,f351])).
% 3.48/0.84  fof(f351,plain,(
% 3.48/0.84    sK19 = sK20),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f350,plain,(
% 3.48/0.84    m1_subset_1(sK20,u1_struct_0(sK16))),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f468,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f184])).
% 3.48/0.84  fof(f184,plain,(
% 3.48/0.84    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.48/0.84    inference(flattening,[],[f183])).
% 3.48/0.84  fof(f183,plain,(
% 3.48/0.84    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.48/0.84    inference(ennf_transformation,[],[f23])).
% 3.48/0.84  fof(f23,axiom,(
% 3.48/0.84    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 3.48/0.84  fof(f4607,plain,(
% 3.48/0.84    ( ! [X0] : (~r2_hidden(sK19,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16))) | ~v3_pre_topc(X0,sK17)) ) | (~spl46_11 | ~spl46_13)),
% 3.48/0.84    inference(subsumption_resolution,[],[f4554,f453])).
% 3.48/0.84  fof(f453,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f299])).
% 3.48/0.84  fof(f299,plain,(
% 3.48/0.84    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.48/0.84    inference(nnf_transformation,[],[f24])).
% 3.48/0.84  fof(f24,axiom,(
% 3.48/0.84    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.48/0.84  fof(f4554,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK16))) | ~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17)) ) | (~spl46_11 | ~spl46_13)),
% 3.48/0.84    inference(backward_demodulation,[],[f3754,f4456])).
% 3.48/0.84  fof(f4456,plain,(
% 3.48/0.84    u1_struct_0(sK16) = u1_struct_0(sK17) | (~spl46_11 | ~spl46_13)),
% 3.48/0.84    inference(subsumption_resolution,[],[f2511,f4454])).
% 3.48/0.84  fof(f4454,plain,(
% 3.48/0.84    r1_tarski(u1_struct_0(sK17),u1_struct_0(sK16)) | ~spl46_13),
% 3.48/0.84    inference(resolution,[],[f4392,f453])).
% 3.48/0.84  fof(f4392,plain,(
% 3.48/0.84    m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK16))) | ~spl46_13),
% 3.48/0.84    inference(resolution,[],[f4383,f384])).
% 3.48/0.84  fof(f384,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~sP4(X0,X1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.48/0.84    inference(cnf_transformation,[],[f263])).
% 3.48/0.84  fof(f4383,plain,(
% 3.48/0.84    sP4(sK16,u1_struct_0(sK17)) | ~spl46_13),
% 3.48/0.84    inference(subsumption_resolution,[],[f4382,f1213])).
% 3.48/0.84  fof(f4382,plain,(
% 3.48/0.84    sP4(sK16,u1_struct_0(sK17)) | ~v2_pre_topc(sK16) | ~spl46_13),
% 3.48/0.84    inference(subsumption_resolution,[],[f4380,f573])).
% 3.48/0.84  fof(f4380,plain,(
% 3.48/0.84    sP4(sK16,u1_struct_0(sK17)) | ~l1_pre_topc(sK16) | ~v2_pre_topc(sK16) | ~spl46_13),
% 3.48/0.84    inference(resolution,[],[f4361,f387])).
% 3.48/0.84  fof(f387,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~sP5(X0,X1) | sP4(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f264])).
% 3.48/0.84  fof(f4361,plain,(
% 3.48/0.84    sP5(sK16,u1_struct_0(sK17)) | ~spl46_13),
% 3.48/0.84    inference(subsumption_resolution,[],[f4351,f1170])).
% 3.48/0.84  fof(f1170,plain,(
% 3.48/0.84    m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17))) | ~spl46_13),
% 3.48/0.84    inference(forward_demodulation,[],[f1161,f797])).
% 3.48/0.84  fof(f797,plain,(
% 3.48/0.84    u1_struct_0(sK17) = k2_struct_0(sK17)),
% 3.48/0.84    inference(resolution,[],[f690,f574])).
% 3.48/0.84  fof(f574,plain,(
% 3.48/0.84    l1_pre_topc(sK17)),
% 3.48/0.84    inference(resolution,[],[f570,f344])).
% 3.48/0.84  fof(f344,plain,(
% 3.48/0.84    m1_pre_topc(sK17,sK14)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f1161,plain,(
% 3.48/0.84    m1_subset_1(k2_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17))) | ~spl46_13),
% 3.48/0.84    inference(resolution,[],[f497,f862])).
% 3.48/0.84  fof(f862,plain,(
% 3.48/0.84    l1_struct_0(sK17) | ~spl46_13),
% 3.48/0.84    inference(avatar_component_clause,[],[f861])).
% 3.48/0.84  fof(f861,plain,(
% 3.48/0.84    spl46_13 <=> l1_struct_0(sK17)),
% 3.48/0.84    introduced(avatar_definition,[new_symbols(naming,[spl46_13])])).
% 3.48/0.84  fof(f4351,plain,(
% 3.48/0.84    sP5(sK16,u1_struct_0(sK17)) | ~m1_subset_1(u1_struct_0(sK17),k1_zfmisc_1(u1_struct_0(sK17)))),
% 3.48/0.84    inference(resolution,[],[f2925,f1237])).
% 3.48/0.84  fof(f1237,plain,(
% 3.48/0.84    v3_pre_topc(u1_struct_0(sK17),sK17)),
% 3.48/0.84    inference(forward_demodulation,[],[f1236,f797])).
% 3.48/0.84  fof(f1236,plain,(
% 3.48/0.84    v3_pre_topc(k2_struct_0(sK17),sK17)),
% 3.48/0.84    inference(subsumption_resolution,[],[f1231,f574])).
% 3.48/0.84  fof(f1231,plain,(
% 3.48/0.84    ~l1_pre_topc(sK17) | v3_pre_topc(k2_struct_0(sK17),sK17)),
% 3.48/0.84    inference(resolution,[],[f1214,f483])).
% 3.48/0.84  fof(f1214,plain,(
% 3.48/0.84    v2_pre_topc(sK17)),
% 3.48/0.84    inference(resolution,[],[f1211,f344])).
% 3.48/0.84  fof(f2925,plain,(
% 3.48/0.84    ( ! [X0] : (~v3_pre_topc(X0,sK17) | sP5(sK16,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))) )),
% 3.48/0.84    inference(superposition,[],[f382,f348])).
% 3.48/0.84  fof(f382,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | sP5(X0,X1) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 3.48/0.84    inference(cnf_transformation,[],[f261])).
% 3.48/0.84  fof(f2511,plain,(
% 3.48/0.84    ~r1_tarski(u1_struct_0(sK17),u1_struct_0(sK16)) | u1_struct_0(sK16) = u1_struct_0(sK17) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f2508,f457])).
% 3.48/0.84  fof(f457,plain,(
% 3.48/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.48/0.84    inference(cnf_transformation,[],[f301])).
% 3.48/0.84  fof(f301,plain,(
% 3.48/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.84    inference(flattening,[],[f300])).
% 3.48/0.84  fof(f300,plain,(
% 3.48/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.48/0.84    inference(nnf_transformation,[],[f5])).
% 3.48/0.84  fof(f5,axiom,(
% 3.48/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.48/0.84  fof(f2508,plain,(
% 3.48/0.84    r1_tarski(u1_struct_0(sK16),u1_struct_0(sK17)) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f2468,f453])).
% 3.48/0.84  fof(f2468,plain,(
% 3.48/0.84    m1_subset_1(u1_struct_0(sK16),k1_zfmisc_1(u1_struct_0(sK17))) | ~spl46_11),
% 3.48/0.84    inference(resolution,[],[f2466,f2242])).
% 3.48/0.84  fof(f2466,plain,(
% 3.48/0.84    ( ! [X0] : (~sP5(sK16,X0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))) )),
% 3.48/0.84    inference(superposition,[],[f381,f348])).
% 3.48/0.84  fof(f381,plain,(
% 3.48/0.84    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~sP5(X0,X1)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f261])).
% 3.48/0.84  fof(f3754,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17)))) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3753,f335])).
% 3.48/0.84  fof(f335,plain,(
% 3.48/0.84    ~v2_struct_0(sK14)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3753,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3752,f336])).
% 3.48/0.84  fof(f3752,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3751,f337])).
% 3.48/0.84  fof(f3751,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3750,f338])).
% 3.48/0.84  fof(f338,plain,(
% 3.48/0.84    ~v2_struct_0(sK15)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3750,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3749,f339])).
% 3.48/0.84  fof(f339,plain,(
% 3.48/0.84    v2_pre_topc(sK15)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3749,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3748,f340])).
% 3.48/0.84  fof(f340,plain,(
% 3.48/0.84    l1_pre_topc(sK15)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3748,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3747,f341])).
% 3.48/0.84  fof(f341,plain,(
% 3.48/0.84    ~v2_struct_0(sK16)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3747,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3746,f343])).
% 3.48/0.84  fof(f343,plain,(
% 3.48/0.84    ~v2_struct_0(sK17)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3746,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3745,f344])).
% 3.48/0.84  fof(f3745,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3744,f345])).
% 3.48/0.84  fof(f345,plain,(
% 3.48/0.84    v1_funct_1(sK18)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3744,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3743,f346])).
% 3.48/0.84  fof(f346,plain,(
% 3.48/0.84    v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15))),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3743,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3742,f347])).
% 3.48/0.84  fof(f347,plain,(
% 3.48/0.84    m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15))))),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3742,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3741,f3374])).
% 3.48/0.84  fof(f3374,plain,(
% 3.48/0.84    m1_pre_topc(sK16,sK17)),
% 3.48/0.84    inference(subsumption_resolution,[],[f3373,f574])).
% 3.48/0.84  fof(f3373,plain,(
% 3.48/0.84    m1_pre_topc(sK16,sK17) | ~l1_pre_topc(sK17)),
% 3.48/0.84    inference(duplicate_literal_removal,[],[f3368])).
% 3.48/0.84  fof(f3368,plain,(
% 3.48/0.84    m1_pre_topc(sK16,sK17) | ~l1_pre_topc(sK17) | ~l1_pre_topc(sK17)),
% 3.48/0.84    inference(resolution,[],[f3360,f437])).
% 3.48/0.84  fof(f437,plain,(
% 3.48/0.84    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f169])).
% 3.48/0.84  fof(f169,plain,(
% 3.48/0.84    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f104])).
% 3.48/0.84  fof(f104,axiom,(
% 3.48/0.84    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 3.48/0.84  fof(f3360,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(sK17,X0) | m1_pre_topc(sK16,X0) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3359,f1214])).
% 3.48/0.84  fof(f3359,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(sK17,X0) | m1_pre_topc(sK16,X0) | ~v2_pre_topc(sK17) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3358,f1213])).
% 3.48/0.84  fof(f3358,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(sK17,X0) | ~v2_pre_topc(sK16) | m1_pre_topc(sK16,X0) | ~v2_pre_topc(sK17) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3357,f573])).
% 3.48/0.84  fof(f3357,plain,(
% 3.48/0.84    ( ! [X0] : (~m1_pre_topc(sK17,X0) | ~l1_pre_topc(sK16) | ~v2_pre_topc(sK16) | m1_pre_topc(sK16,X0) | ~v2_pre_topc(sK17) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3356,f574])).
% 3.48/0.84  fof(f3356,plain,(
% 3.48/0.84    ( ! [X0] : (~l1_pre_topc(sK17) | ~m1_pre_topc(sK17,X0) | ~l1_pre_topc(sK16) | ~v2_pre_topc(sK16) | m1_pre_topc(sK16,X0) | ~v2_pre_topc(sK17) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(superposition,[],[f517,f348])).
% 3.48/0.84  fof(f517,plain,(
% 3.48/0.84    ( ! [X2,X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | m1_pre_topc(X2,X0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(equality_resolution,[],[f396])).
% 3.48/0.84  fof(f396,plain,(
% 3.48/0.84    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f270])).
% 3.48/0.84  fof(f270,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(nnf_transformation,[],[f138])).
% 3.48/0.84  fof(f138,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(flattening,[],[f137])).
% 3.48/0.84  fof(f137,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.48/0.84    inference(ennf_transformation,[],[f102])).
% 3.48/0.84  fof(f102,axiom,(
% 3.48/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).
% 3.48/0.84  fof(f3741,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_pre_topc(sK16,sK17) | ~m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3740,f349])).
% 3.48/0.84  fof(f349,plain,(
% 3.48/0.84    m1_subset_1(sK19,u1_struct_0(sK17))),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3740,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(sK19,u1_struct_0(sK17)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_pre_topc(sK16,sK17) | ~m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3739,f532])).
% 3.48/0.84  fof(f3739,plain,(
% 3.48/0.84    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(sK19,u1_struct_0(sK16)) | ~m1_subset_1(sK19,u1_struct_0(sK17)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_pre_topc(sK16,sK17) | ~m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f3738,f353])).
% 3.48/0.84  fof(f353,plain,(
% 3.48/0.84    ~r1_tmap_1(sK17,sK15,sK18,sK19)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f3738,plain,(
% 3.48/0.84    ( ! [X0] : (r1_tmap_1(sK17,sK15,sK18,sK19) | ~r1_tarski(X0,u1_struct_0(sK16)) | ~r2_hidden(sK19,X0) | ~v3_pre_topc(X0,sK17) | ~m1_subset_1(sK19,u1_struct_0(sK16)) | ~m1_subset_1(sK19,u1_struct_0(sK17)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK17))) | ~m1_pre_topc(sK16,sK17) | ~m1_subset_1(sK18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK17),u1_struct_0(sK15)))) | ~v1_funct_2(sK18,u1_struct_0(sK17),u1_struct_0(sK15)) | ~v1_funct_1(sK18) | ~m1_pre_topc(sK17,sK14) | v2_struct_0(sK17) | v2_struct_0(sK16) | ~l1_pre_topc(sK15) | ~v2_pre_topc(sK15) | v2_struct_0(sK15) | ~l1_pre_topc(sK14) | ~v2_pre_topc(sK14) | v2_struct_0(sK14)) )),
% 3.48/0.84    inference(resolution,[],[f537,f531])).
% 3.48/0.84  fof(f531,plain,(
% 3.48/0.84    r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK19)),
% 3.48/0.84    inference(backward_demodulation,[],[f352,f351])).
% 3.48/0.84  fof(f352,plain,(
% 3.48/0.84    r1_tmap_1(sK16,sK15,k3_tmap_1(sK14,sK15,sK17,sK16,sK18),sK20)),
% 3.48/0.84    inference(cnf_transformation,[],[f241])).
% 3.48/0.84  fof(f537,plain,(
% 3.48/0.84    ( ! [X4,X2,X0,X7,X5,X3,X1] : (~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | r1_tmap_1(X3,X1,X4,X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.84    inference(subsumption_resolution,[],[f510,f432])).
% 3.48/0.84  fof(f432,plain,(
% 3.48/0.84    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f163])).
% 3.48/0.84  fof(f163,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.48/0.84    inference(flattening,[],[f162])).
% 3.48/0.84  fof(f162,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f109])).
% 3.48/0.84  fof(f109,axiom,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 3.48/0.84  fof(f510,plain,(
% 3.48/0.84    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.84    inference(equality_resolution,[],[f371])).
% 3.48/0.84  fof(f371,plain,(
% 3.48/0.84    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f256])).
% 3.48/0.84  fof(f256,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.84    inference(nnf_transformation,[],[f128])).
% 3.48/0.84  fof(f128,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.48/0.84    inference(flattening,[],[f127])).
% 3.48/0.84  fof(f127,plain,(
% 3.48/0.84    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f111])).
% 3.48/0.84  fof(f111,axiom,(
% 3.48/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).
% 3.48/0.84  fof(f871,plain,(
% 3.48/0.84    spl46_13),
% 3.48/0.84    inference(avatar_contradiction_clause,[],[f870])).
% 3.48/0.84  fof(f870,plain,(
% 3.48/0.84    $false | spl46_13),
% 3.48/0.84    inference(subsumption_resolution,[],[f869,f574])).
% 3.48/0.84  fof(f869,plain,(
% 3.48/0.84    ~l1_pre_topc(sK17) | spl46_13),
% 3.48/0.84    inference(resolution,[],[f863,f504])).
% 3.48/0.84  fof(f863,plain,(
% 3.48/0.84    ~l1_struct_0(sK17) | spl46_13),
% 3.48/0.84    inference(avatar_component_clause,[],[f861])).
% 3.48/0.84  fof(f858,plain,(
% 3.48/0.84    spl46_11),
% 3.48/0.84    inference(avatar_contradiction_clause,[],[f857])).
% 3.48/0.84  fof(f857,plain,(
% 3.48/0.84    $false | spl46_11),
% 3.48/0.84    inference(subsumption_resolution,[],[f856,f573])).
% 3.48/0.84  fof(f856,plain,(
% 3.48/0.84    ~l1_pre_topc(sK16) | spl46_11),
% 3.48/0.84    inference(resolution,[],[f850,f504])).
% 3.48/0.84  fof(f850,plain,(
% 3.48/0.84    ~l1_struct_0(sK16) | spl46_11),
% 3.48/0.84    inference(avatar_component_clause,[],[f848])).
% 3.48/0.84  fof(f855,plain,(
% 3.48/0.84    ~spl46_11 | ~spl46_12),
% 3.48/0.84    inference(avatar_split_clause,[],[f818,f852,f848])).
% 3.48/0.84  fof(f818,plain,(
% 3.48/0.84    ~v1_xboole_0(u1_struct_0(sK16)) | ~l1_struct_0(sK16)),
% 3.48/0.84    inference(subsumption_resolution,[],[f817,f341])).
% 3.48/0.84  fof(f817,plain,(
% 3.48/0.84    ~v1_xboole_0(u1_struct_0(sK16)) | ~l1_struct_0(sK16) | v2_struct_0(sK16)),
% 3.48/0.84    inference(superposition,[],[f496,f796])).
% 3.48/0.84  fof(f496,plain,(
% 3.48/0.84    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.48/0.84    inference(cnf_transformation,[],[f205])).
% 3.48/0.84  fof(f205,plain,(
% 3.48/0.84    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.48/0.84    inference(flattening,[],[f204])).
% 3.48/0.84  fof(f204,plain,(
% 3.48/0.84    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.48/0.84    inference(ennf_transformation,[],[f69])).
% 3.48/0.84  fof(f69,axiom,(
% 3.48/0.84    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.48/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 3.48/0.84  % SZS output end Proof for theBenchmark
% 3.48/0.84  % (30737)------------------------------
% 3.48/0.84  % (30737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.84  % (30737)Termination reason: Refutation
% 3.48/0.84  
% 3.48/0.84  % (30737)Memory used [KB]: 8699
% 3.48/0.84  % (30737)Time elapsed: 0.402 s
% 3.48/0.84  % (30737)------------------------------
% 3.48/0.84  % (30737)------------------------------
% 3.48/0.86  % (30699)Success in time 0.495 s
%------------------------------------------------------------------------------
