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
% DateTime   : Thu Dec  3 13:17:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 705 expanded)
%              Number of leaves         :   24 ( 374 expanded)
%              Depth                    :   21
%              Number of atoms          :  924 (9342 expanded)
%              Number of equality atoms :   53 (1279 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f143,f152,f169,f191])).

fof(f191,plain,(
    ~ spl13_2 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f189,f88])).

fof(f88,plain,(
    m1_connsp_2(sK10,sK5,sK6) ),
    inference(backward_demodulation,[],[f61,f59])).

fof(f59,plain,(
    sK6 = sK8 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK9,sK10))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
    & m1_connsp_2(sK10,sK5,sK8)
    & m1_connsp_2(sK9,sK4,sK7)
    & sK6 = sK8
    & sK6 = sK7
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f12,f34,f33,f32,f31,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ! [X8] :
                                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                        | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                    & m1_connsp_2(X7,X2,X5) )
                                & m1_connsp_2(X6,X1,X4) )
                            & X3 = X5
                            & X3 = X4
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
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
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK3,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,X1,X2))) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ m1_connsp_2(X8,k1_tsep_1(sK3,X1,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,X1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,X1,X2))) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK3)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,X2),X3) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,sK4,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK4)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,X2))) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,X2),X3) )
                            & m1_connsp_2(X7,X2,X5) )
                        & m1_connsp_2(X6,sK4,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK4)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,X2))) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),X3) )
                          & m1_connsp_2(X7,sK5,X5) )
                      & m1_connsp_2(X6,sK4,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(sK5)) )
              & m1_subset_1(X4,u1_struct_0(sK4)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),X3) )
                        & m1_connsp_2(X7,sK5,X5) )
                    & m1_connsp_2(X6,sK4,X4) )
                & X3 = X5
                & X3 = X4
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_subset_1(X4,u1_struct_0(sK4)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
                      & m1_connsp_2(X7,sK5,X5) )
                  & m1_connsp_2(X6,sK4,X4) )
              & sK6 = X5
              & sK6 = X4
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & m1_subset_1(X4,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
                    & m1_connsp_2(X7,sK5,X5) )
                & m1_connsp_2(X6,sK4,X4) )
            & sK6 = X5
            & sK6 = X4
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & m1_subset_1(X4,u1_struct_0(sK4)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
                  & m1_connsp_2(X7,sK5,X5) )
              & m1_connsp_2(X6,sK4,sK7) )
          & sK6 = X5
          & sK6 = sK7
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
                & m1_connsp_2(X7,sK5,X5) )
            & m1_connsp_2(X6,sK4,sK7) )
        & sK6 = X5
        & sK6 = sK7
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
              & m1_connsp_2(X7,sK5,sK8) )
          & m1_connsp_2(X6,sK4,sK7) )
      & sK6 = sK8
      & sK6 = sK7
      & m1_subset_1(sK8,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
            & m1_connsp_2(X7,sK5,sK8) )
        & m1_connsp_2(X6,sK4,sK7) )
   => ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(sK9,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
          & m1_connsp_2(X7,sK5,sK8) )
      & m1_connsp_2(sK9,sK4,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X7] :
        ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(sK9,X7))
            | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
        & m1_connsp_2(X7,sK5,sK8) )
   => ( ! [X8] :
          ( ~ r1_tarski(X8,k2_xboole_0(sK9,sK10))
          | ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) )
      & m1_connsp_2(sK10,sK5,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
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
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X3 = X4 )
                             => ! [X6] :
                                  ( m1_connsp_2(X6,X1,X4)
                                 => ! [X7] :
                                      ( m1_connsp_2(X7,X2,X5)
                                     => ? [X8] :
                                          ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                          & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tmap_1)).

fof(f61,plain,(
    m1_connsp_2(sK10,sK5,sK8) ),
    inference(cnf_transformation,[],[f35])).

fof(f189,plain,
    ( ~ m1_connsp_2(sK10,sK5,sK6)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f188,f89])).

fof(f89,plain,(
    m1_connsp_2(sK9,sK4,sK6) ),
    inference(backward_demodulation,[],[f60,f58])).

fof(f58,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_connsp_2(sK9,sK4,sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f188,plain,
    ( ~ m1_connsp_2(sK9,sK4,sK6)
    | ~ m1_connsp_2(sK10,sK5,sK6)
    | ~ spl13_2 ),
    inference(resolution,[],[f187,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | ~ m1_connsp_2(X0,sK5,sK6) ) ),
    inference(subsumption_resolution,[],[f178,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f177,f49])).

fof(f49,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f50,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f175,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ m1_pre_topc(sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f173,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f172,f54])).

fof(f54,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f171,f91])).

fof(f91,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f56,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f170,f90])).

fof(f90,plain,(
    m1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f57,f59])).

fof(f57,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK5,sK6)
      | ~ m1_connsp_2(X1,sK4,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
      | sP2(X0,X1,sK6,sK5,sK4,sK3)
      | ~ m1_pre_topc(sK5,sK3)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK3)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,(
    m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | sP2(X7,X6,X5,X2,X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( sP2(X7,X6,X5,X2,X1,X0)
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP2(X7,X6,X3,X2,X1,X0)
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X4)
      | X3 != X5
      | X3 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( sP2(X7,X6,X3,X2,X1,X0)
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f25])).

fof(f25,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
      | ~ sP2(X7,X6,X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
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
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ? [X8] :
                                      ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                      & r2_hidden(X3,X8)
                                      & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  | ~ m1_connsp_2(X7,X2,X5) )
                              | ~ m1_connsp_2(X6,X1,X4) )
                          | X3 != X5
                          | X3 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & r2_hidden(X3,X8)
                                        & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tmap_1)).

fof(f187,plain,
    ( ~ sP2(sK10,sK9,sK6,sK5,sK4,sK3)
    | ~ spl13_2 ),
    inference(resolution,[],[f186,f181])).

fof(f181,plain,
    ( ~ sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5))
    | ~ spl13_2 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ~ sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5))
    | ~ sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5))
    | ~ spl13_2 ),
    inference(resolution,[],[f126,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK11(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( r2_hidden(X0,sK11(X0,X1,X2))
          & r1_tarski(sK11(X0,X1,X2),X1)
          & v3_pre_topc(sK11(X0,X1,X2),X2)
          & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X0,sK11(X0,X1,X2))
        & r1_tarski(sK11(X0,X1,X2),X1)
        & v3_pre_topc(sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( r2_hidden(X0,X4)
            & r1_tarski(X4,X1)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X1,X3)
            | ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( r2_hidden(X1,X3)
            & r1_tarski(X3,X2)
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10))
        | ~ sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5)) )
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl13_2
  <=> ! [X0] :
        ( ~ sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5))
        | ~ r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f186,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X2,k2_xboole_0(X1,X0),k1_tsep_1(X5,X4,X3))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5)
      | sP0(X2,k2_xboole_0(X1,X0),k1_tsep_1(X5,X4,X3))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f183,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0))
        & r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5))
        & v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3))
        & m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3)))) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f43,f44])).

fof(f44,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(X6,k2_xboole_0(X1,X0))
          & r2_hidden(X2,X6)
          & v3_pre_topc(X6,k1_tsep_1(X5,X4,X3))
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3)))) )
     => ( r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0))
        & r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5))
        & v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3))
        & m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ? [X6] :
          ( r1_tarski(X6,k2_xboole_0(X1,X0))
          & r2_hidden(X2,X6)
          & v3_pre_topc(X6,k1_tsep_1(X5,X4,X3))
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3)))) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
      | ~ sP2(X7,X6,X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f183,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(sK12(X0,X1,X2,X3,X4,X5),X6)
      | ~ sP2(X0,X1,X2,X3,X4,X5)
      | sP0(X2,X6,k1_tsep_1(X5,X4,X3)) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5)
      | ~ r1_tarski(sK12(X0,X1,X2,X3,X4,X5),X6)
      | sP0(X2,X6,k1_tsep_1(X5,X4,X3))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(resolution,[],[f111,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] :
      ( ~ r2_hidden(X13,sK12(X7,X8,X9,X10,X11,X12))
      | ~ sP2(X7,X8,X9,X10,X11,X12)
      | ~ r1_tarski(sK12(X7,X8,X9,X10,X11,X12),X14)
      | sP0(X13,X14,k1_tsep_1(X12,X11,X10)) ) ),
    inference(subsumption_resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,(
    ! [X14,X12,X10,X8,X7,X13,X11,X9] :
      ( ~ sP2(X7,X8,X9,X10,X11,X12)
      | ~ r2_hidden(X13,sK12(X7,X8,X9,X10,X11,X12))
      | ~ r1_tarski(sK12(X7,X8,X9,X10,X11,X12),X14)
      | ~ v3_pre_topc(sK12(X7,X8,X9,X10,X11,X12),k1_tsep_1(X12,X11,X10))
      | sP0(X13,X14,k1_tsep_1(X12,X11,X10)) ) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,X1)
      | ~ v3_pre_topc(X3,X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3))))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f169,plain,(
    ~ spl13_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f167,plain,
    ( v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f164,f52])).

fof(f164,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f163,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f154,f54])).

fof(f154,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl13_3 ),
    inference(resolution,[],[f130,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f130,plain,
    ( v2_struct_0(k1_tsep_1(sK3,sK4,sK5))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl13_3
  <=> v2_struct_0(k1_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f152,plain,(
    spl13_4 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl13_4 ),
    inference(subsumption_resolution,[],[f150,f48])).

fof(f150,plain,
    ( v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f149,f49])).

fof(f149,plain,
    ( ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f148,f50])).

fof(f148,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f147,f51])).

fof(f147,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f146,f52])).

fof(f146,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(subsumption_resolution,[],[f144,f54])).

fof(f144,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | spl13_4 ),
    inference(resolution,[],[f134,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f134,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK3,sK4,sK5))
    | spl13_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl13_4
  <=> v2_pre_topc(k1_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f143,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl13_1 ),
    inference(subsumption_resolution,[],[f141,f54])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f140,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f139,f50])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f138,f51])).

fof(f138,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f136,f53])).

fof(f136,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | spl13_1 ),
    inference(resolution,[],[f123,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | l1_pre_topc(k1_tsep_1(X1,X2,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f83,f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f123,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK3,sK4,sK5))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl13_1
  <=> l1_pre_topc(k1_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f135,plain,
    ( ~ spl13_1
    | spl13_2
    | spl13_3
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f117,f132,f128,f125,f121])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(k1_tsep_1(sK3,sK4,sK5))
      | v2_struct_0(k1_tsep_1(sK3,sK4,sK5))
      | ~ sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5))
      | ~ l1_pre_topc(k1_tsep_1(sK3,sK4,sK5))
      | ~ r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(k1_tsep_1(sK3,sK4,sK5))
      | v2_struct_0(k1_tsep_1(sK3,sK4,sK5))
      | ~ sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5))
      | ~ m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))
      | ~ l1_pre_topc(k1_tsep_1(sK3,sK4,sK5))
      | ~ r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10)) ) ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X8] :
      ( ~ m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)
      | ~ r1_tarski(X8,k2_xboole_0(sK9,sK10)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK11(X1,X2,X0),X0,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK11(X1,X2,X0),X0,X1)
      | ~ sP0(X1,X2,X0) ) ),
    inference(resolution,[],[f112,f107])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,sK11(X3,X4,X5),X5)
      | ~ sP0(X3,X4,X5) ) ),
    inference(resolution,[],[f105,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK11(X0,X1,X2),X3)
      | sP0(X0,X3,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(sK11(X0,X1,X2),X3)
      | sP0(X0,X3,X2)
      | ~ sP0(X0,X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK11(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,sK11(X1,X2,X3))
      | ~ r1_tarski(sK11(X1,X2,X3),X4)
      | sP0(X0,X4,X3)
      | ~ sP0(X1,X2,X3) ) ),
    inference(subsumption_resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK11(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,sK11(X1,X2,X3))
      | ~ r1_tarski(sK11(X1,X2,X3),X4)
      | ~ v3_pre_topc(sK11(X1,X2,X3),X3)
      | sP0(X0,X4,X3)
      | ~ sP0(X1,X2,X3) ) ),
    inference(resolution,[],[f70,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,sK11(X2,X3,X1),X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ sP0(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | m1_connsp_2(sK11(X2,X3,X1),X1,X0) ) ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_connsp_2(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ m1_connsp_2(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( ( m1_connsp_2(X2,X0,X1)
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ m1_connsp_2(X2,X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( m1_connsp_2(X2,X0,X1)
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,sK11(X1,X2,X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ sP0(X1,X2,X0) ) ),
    inference(resolution,[],[f71,f66])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f23,f22])).

% (11539)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (11518)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (11519)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (11518)Refutation not found, incomplete strategy% (11518)------------------------------
% 0.22/0.50  % (11518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11518)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11518)Memory used [KB]: 10746
% 0.22/0.50  % (11518)Time elapsed: 0.092 s
% 0.22/0.50  % (11518)------------------------------
% 0.22/0.50  % (11518)------------------------------
% 0.22/0.50  % (11530)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (11544)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (11522)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (11527)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (11531)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (11541)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (11537)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (11544)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f135,f143,f152,f169,f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ~spl13_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f190])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    $false | ~spl13_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f189,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    m1_connsp_2(sK10,sK5,sK6)),
% 0.22/0.51    inference(backward_demodulation,[],[f61,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    sK6 = sK8),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    (((((((! [X8] : (~r1_tarski(X8,k2_xboole_0(sK9,sK10)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(sK10,sK5,sK8)) & m1_connsp_2(sK9,sK4,sK7)) & sK6 = sK8 & sK6 = sK7 & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f12,f34,f33,f32,f31,f30,f29,f28,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,X1,X2)))) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,X1,X2)))) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,sK4,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,X2)))) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,sK4,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,X2)))) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),X3)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),X3)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,X4)) & sK6 = X5 & sK6 = X4 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,X4)) & sK6 = X5 & sK6 = X4 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(sK4))) => (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,sK7)) & sK6 = X5 & sK6 = sK7 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,X5)) & m1_connsp_2(X6,sK4,sK7)) & sK6 = X5 & sK6 = sK7 & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,sK8)) & m1_connsp_2(X6,sK4,sK7)) & sK6 = sK8 & sK6 = sK7 & m1_subset_1(sK8,u1_struct_0(sK5)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,sK8)) & m1_connsp_2(X6,sK4,sK7)) => (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK9,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,sK8)) & m1_connsp_2(sK9,sK4,sK7))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK9,X7)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(X7,sK5,sK8)) => (! [X8] : (~r1_tarski(X8,k2_xboole_0(sK9,sK10)) | ~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6)) & m1_connsp_2(sK10,sK5,sK8))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & X3 = X5 & X3 = X4 & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : (? [X7] : (! [X8] : (~r1_tarski(X8,k2_xboole_0(X6,X7)) | ~m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)) & m1_connsp_2(X7,X2,X5)) & m1_connsp_2(X6,X1,X4)) & (X3 = X5 & X3 = X4)) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f7])).
% 0.22/0.51  fof(f7,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & m1_connsp_2(X8,k1_tsep_1(X0,X1,X2),X3)))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tmap_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    m1_connsp_2(sK10,sK5,sK8)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ~m1_connsp_2(sK10,sK5,sK6) | ~spl13_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    m1_connsp_2(sK9,sK4,sK6)),
% 0.22/0.51    inference(backward_demodulation,[],[f60,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    sK6 = sK7),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    m1_connsp_2(sK9,sK4,sK7)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~m1_connsp_2(sK9,sK4,sK6) | ~m1_connsp_2(sK10,sK5,sK6) | ~spl13_2),
% 0.22/0.51    inference(resolution,[],[f187,f179])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP2(X0,X1,sK6,sK5,sK4,sK3) | ~m1_connsp_2(X1,sK4,sK6) | ~m1_connsp_2(X0,sK5,sK6)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f178,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f177,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v2_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f175,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ~v2_struct_0(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m1_pre_topc(sK4,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~v2_struct_0(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    m1_pre_topc(sK5,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK4))),
% 0.22/0.51    inference(forward_demodulation,[],[f56,f58])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    m1_subset_1(sK7,u1_struct_0(sK4))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f170,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(sK5))),
% 0.22/0.51    inference(forward_demodulation,[],[f57,f59])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    m1_subset_1(sK8,u1_struct_0(sK5))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_connsp_2(X0,sK5,sK6) | ~m1_connsp_2(X1,sK4,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK5)) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | sP2(X0,X1,sK6,sK5,sK4,sK3) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.51    inference(resolution,[],[f85,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5)))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X7,X5,X1] : (~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | sP2(X7,X6,X5,X2,X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X1] : (sP2(X7,X6,X5,X2,X1,X0) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP2(X7,X6,X3,X2,X1,X0) | ~m1_connsp_2(X7,X2,X5) | ~m1_connsp_2(X6,X1,X4) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (sP2(X7,X6,X3,X2,X1,X0) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(definition_folding,[],[f17,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X7,X6,X3,X2,X1,X0] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~sP2(X7,X6,X3,X2,X1,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | X3 != X5 | X3 != X4 | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : (! [X7] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~m1_connsp_2(X7,X2,X5)) | ~m1_connsp_2(X6,X1,X4)) | (X3 != X5 | X3 != X4)) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ((X3 = X5 & X3 = X4) => ! [X6] : (m1_connsp_2(X6,X1,X4) => ! [X7] : (m1_connsp_2(X7,X2,X5) => ? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tmap_1)).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ~sP2(sK10,sK9,sK6,sK5,sK4,sK3) | ~spl13_2),
% 0.22/0.51    inference(resolution,[],[f186,f181])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ~sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5)) | ~spl13_2),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f180])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5)) | ~sP0(sK6,k2_xboole_0(sK9,sK10),k1_tsep_1(sK3,sK4,sK5)) | ~spl13_2),
% 0.22/0.51    inference(resolution,[],[f126,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(sK11(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK11(X0,X1,X2)) & r1_tarski(sK11(X0,X1,X2),X1) & v3_pre_topc(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f39,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK11(X0,X1,X2)) & r1_tarski(sK11(X0,X1,X2),X1) & v3_pre_topc(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10)) | ~sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5))) ) | ~spl13_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl13_2 <=> ! [X0] : (~sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5)) | ~r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X2,k2_xboole_0(X1,X0),k1_tsep_1(X5,X4,X3)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f184])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5) | sP0(X2,k2_xboole_0(X1,X0),k1_tsep_1(X5,X4,X3)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(resolution,[],[f183,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0)) & r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5)) & v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3)) & m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3))))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (r1_tarski(X6,k2_xboole_0(X1,X0)) & r2_hidden(X2,X6) & v3_pre_topc(X6,k1_tsep_1(X5,X4,X3)) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3))))) => (r1_tarski(sK12(X0,X1,X2,X3,X4,X5),k2_xboole_0(X1,X0)) & r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5)) & v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3)) & m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3))))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : (? [X6] : (r1_tarski(X6,k2_xboole_0(X1,X0)) & r2_hidden(X2,X6) & v3_pre_topc(X6,k1_tsep_1(X5,X4,X3)) & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3))))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 0.22/0.51    inference(rectify,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X7,X6,X3,X2,X1,X0] : (? [X8] : (r1_tarski(X8,k2_xboole_0(X6,X7)) & r2_hidden(X3,X8) & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2)) & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))) | ~sP2(X7,X6,X3,X2,X1,X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f25])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r1_tarski(sK12(X0,X1,X2,X3,X4,X5),X6) | ~sP2(X0,X1,X2,X3,X4,X5) | sP0(X2,X6,k1_tsep_1(X5,X4,X3))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5) | ~r1_tarski(sK12(X0,X1,X2,X3,X4,X5),X6) | sP0(X2,X6,k1_tsep_1(X5,X4,X3)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(resolution,[],[f111,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X2,sK12(X0,X1,X2,X3,X4,X5)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (~r2_hidden(X13,sK12(X7,X8,X9,X10,X11,X12)) | ~sP2(X7,X8,X9,X10,X11,X12) | ~r1_tarski(sK12(X7,X8,X9,X10,X11,X12),X14) | sP0(X13,X14,k1_tsep_1(X12,X11,X10))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v3_pre_topc(sK12(X0,X1,X2,X3,X4,X5),k1_tsep_1(X5,X4,X3)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X14,X12,X10,X8,X7,X13,X11,X9] : (~sP2(X7,X8,X9,X10,X11,X12) | ~r2_hidden(X13,sK12(X7,X8,X9,X10,X11,X12)) | ~r1_tarski(sK12(X7,X8,X9,X10,X11,X12),X14) | ~v3_pre_topc(sK12(X7,X8,X9,X10,X11,X12),k1_tsep_1(X12,X11,X10)) | sP0(X13,X14,k1_tsep_1(X12,X11,X10))) )),
% 0.22/0.51    inference(resolution,[],[f72,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(sK12(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X3)))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~spl13_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    $false | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f48])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f166,f50])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f51])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f52])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f53])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f54])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~spl13_3),
% 0.22/0.51    inference(resolution,[],[f130,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    v2_struct_0(k1_tsep_1(sK3,sK4,sK5)) | ~spl13_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl13_3 <=> v2_struct_0(k1_tsep_1(sK3,sK4,sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    spl13_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    $false | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f48])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f149,f49])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f50])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f51])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f52])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f53])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f144,f54])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | spl13_4),
% 0.22/0.51    inference(resolution,[],[f134,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ~v2_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | spl13_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl13_4 <=> v2_pre_topc(k1_tsep_1(sK3,sK4,sK5))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl13_1),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    $false | spl13_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f54])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f48])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    v2_struct_0(sK3) | ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f50])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f51])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f52])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.52    inference(subsumption_resolution,[],[f136,f53])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_pre_topc(sK5,sK3) | spl13_1),
% 0.22/0.52    inference(resolution,[],[f123,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (l1_pre_topc(k1_tsep_1(X1,X2,X0)) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | v2_struct_0(X1) | l1_pre_topc(k1_tsep_1(X1,X2,X0)) | ~l1_pre_topc(X1)) )),
% 0.22/0.52    inference(resolution,[],[f83,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ~l1_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | spl13_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl13_1 <=> l1_pre_topc(k1_tsep_1(sK3,sK4,sK5))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~spl13_1 | spl13_2 | spl13_3 | ~spl13_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f117,f132,f128,f125,f121])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | v2_struct_0(k1_tsep_1(sK3,sK4,sK5)) | ~sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5)) | ~l1_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | ~r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f116,f55])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | v2_struct_0(k1_tsep_1(sK3,sK4,sK5)) | ~sP0(sK6,X0,k1_tsep_1(sK3,sK4,sK5)) | ~m1_subset_1(sK6,u1_struct_0(k1_tsep_1(sK3,sK4,sK5))) | ~l1_pre_topc(k1_tsep_1(sK3,sK4,sK5)) | ~r1_tarski(sK11(sK6,X0,k1_tsep_1(sK3,sK4,sK5)),k2_xboole_0(sK9,sK10))) )),
% 0.22/0.52    inference(resolution,[],[f115,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X8] : (~m1_connsp_2(X8,k1_tsep_1(sK3,sK4,sK5),sK6) | ~r1_tarski(X8,k2_xboole_0(sK9,sK10))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_connsp_2(sK11(X1,X2,X0),X0,X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f114])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_connsp_2(sK11(X1,X2,X0),X0,X1) | ~sP0(X1,X2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f112,f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    ( ! [X4,X5,X3] : (sP0(X3,sK11(X3,X4,X5),X5) | ~sP0(X3,X4,X5)) )),
% 0.22/0.52    inference(resolution,[],[f105,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK11(X0,X1,X2),X3) | sP0(X0,X3,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f104])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(sK11(X0,X1,X2),X3) | sP0(X0,X3,X2) | ~sP0(X0,X1,X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(resolution,[],[f99,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,sK11(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,sK11(X1,X2,X3)) | ~r1_tarski(sK11(X1,X2,X3),X4) | sP0(X0,X4,X3) | ~sP0(X1,X2,X3)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f98,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v3_pre_topc(sK11(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,sK11(X1,X2,X3)) | ~r1_tarski(sK11(X1,X2,X3),X4) | ~v3_pre_topc(sK11(X1,X2,X3),X3) | sP0(X0,X4,X3) | ~sP0(X1,X2,X3)) )),
% 0.22/0.52    inference(resolution,[],[f70,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~sP0(X0,sK11(X2,X3,X1),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~sP0(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | m1_connsp_2(sK11(X2,X3,X1),X1,X0)) )),
% 0.22/0.52    inference(resolution,[],[f101,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | m1_connsp_2(X1,X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((m1_connsp_2(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~m1_connsp_2(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X2,X1] : (((m1_connsp_2(X2,X0,X1) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~m1_connsp_2(X2,X0,X1))) | ~sP1(X0,X2,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X2,X1] : ((m1_connsp_2(X2,X0,X1) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (sP1(X0,sK11(X1,X2,X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~sP0(X1,X2,X0)) )),
% 0.22/0.52    inference(resolution,[],[f71,f66])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(definition_folding,[],[f15,f23,f22])).
% 0.22/0.52  % (11539)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (11544)------------------------------
% 0.22/0.52  % (11544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11544)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (11544)Memory used [KB]: 10746
% 0.22/0.52  % (11544)Time elapsed: 0.108 s
% 0.22/0.52  % (11544)------------------------------
% 0.22/0.52  % (11544)------------------------------
% 0.22/0.52  % (11528)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (11521)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (11514)Success in time 0.159 s
%------------------------------------------------------------------------------
