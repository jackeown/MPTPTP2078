%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1712+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:23 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 548 expanded)
%              Number of leaves         :   15 ( 302 expanded)
%              Depth                    :   43
%              Number of atoms          :  994 (8194 expanded)
%              Number of equality atoms :   56 (1136 expanded)
%              Maximal formula depth    :   27 (  12 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(subsumption_resolution,[],[f356,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
        | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
    & m1_connsp_2(sK7,sK2,sK5)
    & m1_connsp_2(sK6,sK1,sK4)
    & sK3 = sK5
    & sK3 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f54,f53,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
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
                                      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ m1_connsp_2(X8,k1_tsep_1(sK0,X1,X2),X3) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,X1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,sK1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,X2),X3) )
                            & m1_connsp_2(X7,X2,X5) )
                        & m1_connsp_2(X6,sK1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3) )
                          & m1_connsp_2(X7,sK2,X5) )
                      & m1_connsp_2(X6,sK1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),X3) )
                        & m1_connsp_2(X7,sK2,X5) )
                    & m1_connsp_2(X6,sK1,X4) )
                & X3 = X5
                & X3 = X4
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                      & m1_connsp_2(X7,sK2,X5) )
                  & m1_connsp_2(X6,sK1,X4) )
              & sK3 = X5
              & sK3 = X4
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                    & m1_connsp_2(X7,sK2,X5) )
                & m1_connsp_2(X6,sK1,X4) )
            & sK3 = X5
            & sK3 = X4
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                  & m1_connsp_2(X7,sK2,X5) )
              & m1_connsp_2(X6,sK1,sK4) )
          & sK3 = X5
          & sK3 = sK4
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
                & m1_connsp_2(X7,sK2,X5) )
            & m1_connsp_2(X6,sK1,sK4) )
        & sK3 = X5
        & sK3 = sK4
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
              & m1_connsp_2(X7,sK2,sK5) )
          & m1_connsp_2(X6,sK1,sK4) )
      & sK3 = sK5
      & sK3 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
            & m1_connsp_2(X7,sK2,sK5) )
        & m1_connsp_2(X6,sK1,sK4) )
   => ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
              | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
          & m1_connsp_2(X7,sK2,sK5) )
      & m1_connsp_2(sK6,sK1,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X7] :
        ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
            | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
        & m1_connsp_2(X7,sK2,sK5) )
   => ( ! [X8] :
          ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
          | ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3) )
      & m1_connsp_2(sK7,sK2,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tmap_1)).

fof(f356,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f355,f66])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f355,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f354,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f354,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f353,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f353,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f352,f69])).

fof(f69,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f352,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f351,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f351,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f350,f71])).

fof(f71,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f350,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f349,f112])).

fof(f112,plain,(
    m1_connsp_2(sK6,sK1,sK3) ),
    inference(backward_demodulation,[],[f77,f75])).

fof(f75,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    m1_connsp_2(sK6,sK1,sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f349,plain,
    ( ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f348,f111])).

fof(f111,plain,(
    m1_connsp_2(sK7,sK2,sK3) ),
    inference(backward_demodulation,[],[f78,f76])).

fof(f76,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f78,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f348,plain,
    ( ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f347,f113])).

fof(f113,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f74,f76])).

fof(f74,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f347,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f346,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f346,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f345,f114])).

fof(f114,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f73,f75])).

fof(f73,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f345,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_connsp_2(sK7,sK2,sK3)
    | ~ m1_connsp_2(sK6,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f325,f106])).

fof(f106,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK9(X0,X1,X2,X5,X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r2_hidden(X5,sK9(X0,X1,X2,X5,X6,X7))
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
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
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
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ! [X7] :
                                  ( ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
                                    & r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
                                    & v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
                                    & m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f33,f58])).

% (3396)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f58,plain,(
    ! [X7,X6,X3,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(X8,k2_xboole_0(X6,X7))
          & r2_hidden(X3,X8)
          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
        & r2_hidden(X3,sK9(X0,X1,X2,X3,X6,X7))
        & v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).

fof(f325,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f324,f65])).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f323,f66])).

fof(f323,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f322,f67])).

fof(f322,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f321,f68])).

% (3385)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f321,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f320,f69])).

fof(f320,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f319,f70])).

fof(f319,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f318,f71])).

fof(f318,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X0,sK6,sK7))
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ m1_connsp_2(sK7,sK2,X0)
      | ~ m1_connsp_2(sK6,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f316,f104])).

fof(f104,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK9(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( r1_tarski(sK9(X0,X1,X2,X5,X6,X7),k2_xboole_0(X6,X7))
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
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tarski(sK9(X0,X1,X2,X3,X6,X7),k2_xboole_0(X6,X7))
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
    inference(cnf_transformation,[],[f59])).

fof(f316,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ m1_connsp_2(X0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f315,f72])).

fof(f315,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f314,f65])).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f313,f66])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f312,f67])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f311,f68])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f310,f69])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f309,f70])).

fof(f309,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(subsumption_resolution,[],[f300,f71])).

fof(f300,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,sK1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK3,sK9(sK0,sK1,sK2,X1,X0,X2))
      | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
      | ~ m1_connsp_2(X2,sK2,X1)
      | ~ r1_tarski(sK9(sK0,sK1,sK2,X1,X0,X2),k2_xboole_0(sK6,sK7)) ) ),
    inference(resolution,[],[f189,f79])).

fof(f79,plain,(
    ! [X8] :
      ( ~ m1_connsp_2(X8,k1_tsep_1(sK0,sK1,sK2),sK3)
      | ~ r1_tarski(X8,k2_xboole_0(sK6,sK7)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f189,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( m1_connsp_2(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK9(X5,X4,X1,X2,X3,X0))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_connsp_2(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f188,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f188,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK9(X5,X4,X1,X2,X3,X0))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | m1_connsp_2(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | v2_struct_0(k1_tsep_1(X5,X4,X1)) ) ),
    inference(subsumption_resolution,[],[f187,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | v2_pre_topc(k1_tsep_1(X1,X2,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f102,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f187,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK9(X5,X4,X1,X2,X3,X0))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | m1_connsp_2(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | ~ v2_pre_topc(k1_tsep_1(X5,X4,X1))
      | v2_struct_0(k1_tsep_1(X5,X4,X1)) ) ),
    inference(subsumption_resolution,[],[f186,f156])).

fof(f156,plain,(
    ! [X4,X5,X3] :
      ( l1_pre_topc(k1_tsep_1(X4,X5,X3))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,X4)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | v2_struct_0(X4)
      | l1_pre_topc(k1_tsep_1(X4,X5,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f102,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f186,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK9(X5,X4,X1,X2,X3,X0))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | m1_connsp_2(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | ~ l1_pre_topc(k1_tsep_1(X5,X4,X1))
      | ~ v2_pre_topc(k1_tsep_1(X5,X4,X1))
      | v2_struct_0(k1_tsep_1(X5,X4,X1)) ) ),
    inference(subsumption_resolution,[],[f180,f108])).

fof(f108,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X5,X6,X7),k1_tsep_1(X0,X1,X2))
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
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2,X3,X6,X7),k1_tsep_1(X0,X1,X2))
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
    inference(cnf_transformation,[],[f59])).

fof(f180,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | ~ m1_connsp_2(X3,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X4))
      | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | ~ m1_pre_topc(X1,X5)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X4,X5)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ r2_hidden(X6,sK9(X5,X4,X1,X2,X3,X0))
      | ~ v3_pre_topc(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1))
      | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X5,X4,X1)))
      | m1_connsp_2(sK9(X5,X4,X1,X2,X3,X0),k1_tsep_1(X5,X4,X1),X6)
      | ~ l1_pre_topc(k1_tsep_1(X5,X4,X1))
      | ~ v2_pre_topc(k1_tsep_1(X5,X4,X1))
      | v2_struct_0(k1_tsep_1(X5,X4,X1)) ) ),
    inference(resolution,[],[f110,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_connsp_2(X1,X0,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f110,plain,(
    ! [X6,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_connsp_2(X7,X2,X5)
      | ~ m1_connsp_2(X6,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X6,X4,X2,X0,X7,X5,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X5,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
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
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X6,X7),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
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
    inference(cnf_transformation,[],[f59])).

%------------------------------------------------------------------------------
