%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t20_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:11 EDT 2019

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  211 (7171 expanded)
%              Number of leaves         :   37 (4138 expanded)
%              Depth                    :   20
%              Number of atoms          : 1014 (120575 expanded)
%              Number of equality atoms :   37 (14994 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f651,f665,f689,f729,f763,f802,f959,f1403,f2210,f2219,f2226,f2243,f2261,f2281,f2297,f2319,f4128,f5605,f5640,f5668])).

fof(f5668,plain,(
    spl14_1059 ),
    inference(avatar_contradiction_clause,[],[f5666])).

fof(f5666,plain,
    ( $false
    | ~ spl14_1059 ),
    inference(subsumption_resolution,[],[f515,f5604])).

fof(f5604,plain,
    ( ~ r1_tarski(sK9(sK2,sK4,sK7),sK7)
    | ~ spl14_1059 ),
    inference(avatar_component_clause,[],[f5603])).

fof(f5603,plain,
    ( spl14_1059
  <=> ~ r1_tarski(sK9(sK2,sK4,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1059])])).

fof(f515,plain,(
    r1_tarski(sK9(sK2,sK4,sK7),sK7) ),
    inference(global_subsumption,[],[f185,f514])).

fof(f514,plain,
    ( r1_tarski(sK9(sK2,sK4,sK7),sK7)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f245,f188])).

fof(f188,plain,(
    m1_connsp_2(sK7,sK2,sK4) ),
    inference(forward_demodulation,[],[f119,f165])).

fof(f165,plain,(
    sK4 = sK5 ),
    inference(definition_unfolding,[],[f116,f117])).

fof(f117,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
        | ~ r2_hidden(sK3,X8)
        | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f89,f88,f87,f86,f85,f84,f83,f82])).

fof(f82,plain,
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
                                        | ~ r2_hidden(X3,X8)
                                        | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)))) )
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

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ r2_hidden(X3,X8)
                                    | ~ v3_pre_topc(X8,k1_tsep_1(X0,sK1,X2))
                                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK1,X2)))) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,sK1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK1,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ r2_hidden(X3,X8)
                                  | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,X1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ r2_hidden(X3,X8)
                                | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,sK2))
                                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,sK2)))) )
                            & m1_connsp_2(X7,sK2,X5) )
                        & m1_connsp_2(X6,X1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK2))) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ r2_hidden(X3,X8)
                              | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          & m1_connsp_2(X7,X2,X5) )
                      & m1_connsp_2(X6,X1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(X2)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ r2_hidden(sK3,X8)
                            | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                        & m1_connsp_2(X7,X2,X5) )
                    & m1_connsp_2(X6,X1,X4) )
                & sK3 = X5
                & sK3 = X4
                & m1_subset_1(X5,u1_struct_0(X2)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ r2_hidden(X3,X8)
                          | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                          | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                      & m1_connsp_2(X7,X2,X5) )
                  & m1_connsp_2(X6,X1,X4) )
              & X3 = X5
              & X3 = X4
              & m1_subset_1(X5,u1_struct_0(X2)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ r2_hidden(X3,X8)
                        | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                    & m1_connsp_2(X7,X2,X5) )
                & m1_connsp_2(X6,X1,sK4) )
            & X3 = X5
            & sK4 = X3
            & m1_subset_1(X5,u1_struct_0(X2)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ r2_hidden(X3,X8)
                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                  & m1_connsp_2(X7,X2,X5) )
              & m1_connsp_2(X6,X1,X4) )
          & X3 = X5
          & X3 = X4
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ r2_hidden(X3,X8)
                    | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                & m1_connsp_2(X7,X2,sK5) )
            & m1_connsp_2(X6,X1,X4) )
        & sK5 = X3
        & X3 = X4
        & m1_subset_1(sK5,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ r2_hidden(X3,X8)
                  | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
              & m1_connsp_2(X7,X2,X5) )
          & m1_connsp_2(X6,X1,X4) )
     => ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
                | ~ r2_hidden(X3,X8)
                | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
            & m1_connsp_2(X7,X2,X5) )
        & m1_connsp_2(sK6,X1,X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
              | ~ r2_hidden(X3,X8)
              | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
          & m1_connsp_2(X7,X2,X5) )
     => ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(X6,sK7))
            | ~ r2_hidden(X3,X8)
            | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
        & m1_connsp_2(sK7,X2,X5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
                                          & r2_hidden(X3,X8)
                                          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',t20_tmap_1)).

fof(f116,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f90])).

fof(f119,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f90])).

fof(f245,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK7,sK2,X2)
      | r1_tarski(sK9(sK2,X2,sK7),sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f111,f183,f184,f237])).

fof(f237,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK7,sK2,X2)
      | r1_tarski(sK9(sK2,X2,sK7),sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_tarski(sK9(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK9(X0,X1,X2))
                    & r1_tarski(sK9(X0,X1,X2),X2)
                    & v3_pre_topc(sK9(X0,X1,X2),X0)
                    & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f94,f95])).

fof(f95,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK9(X0,X1,X2))
        & r1_tarski(sK9(X0,X1,X2),X2)
        & v3_pre_topc(sK9(X0,X1,X2),X0)
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
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
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',t8_connsp_2)).

fof(f190,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f111,f183,f185,f184,f189])).

fof(f189,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f188,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',dt_m1_connsp_2)).

fof(f184,plain,(
    l1_pre_topc(sK2) ),
    inference(global_subsumption,[],[f108,f180])).

fof(f180,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f112,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',dt_m1_pre_topc)).

fof(f112,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f108,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f183,plain,(
    v2_pre_topc(sK2) ),
    inference(global_subsumption,[],[f107,f108,f179])).

fof(f179,plain,
    ( v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f112,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',cc1_pre_topc)).

fof(f107,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f111,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

fof(f185,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f115,f165])).

fof(f115,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f90])).

fof(f5640,plain,(
    spl14_1057 ),
    inference(avatar_contradiction_clause,[],[f5638])).

fof(f5638,plain,
    ( $false
    | ~ spl14_1057 ),
    inference(subsumption_resolution,[],[f509,f5601])).

fof(f5601,plain,
    ( ~ r1_tarski(sK9(sK1,sK4,sK6),sK6)
    | ~ spl14_1057 ),
    inference(avatar_component_clause,[],[f5600])).

fof(f5600,plain,
    ( spl14_1057
  <=> ~ r1_tarski(sK9(sK1,sK4,sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1057])])).

fof(f509,plain,(
    r1_tarski(sK9(sK1,sK4,sK6),sK6) ),
    inference(global_subsumption,[],[f114,f508])).

fof(f508,plain,
    ( r1_tarski(sK9(sK1,sK4,sK6),sK6)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[],[f202,f118])).

fof(f118,plain,(
    m1_connsp_2(sK6,sK1,sK4) ),
    inference(cnf_transformation,[],[f90])).

fof(f202,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK6,sK1,X2)
      | r1_tarski(sK9(sK1,X2,sK6),sK6)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f109,f175,f176,f194])).

fof(f194,plain,(
    ! [X2] :
      ( ~ m1_connsp_2(sK6,sK1,X2)
      | r1_tarski(sK9(sK1,X2,sK6),sK6)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f187,f131])).

fof(f187,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_subsumption,[],[f109,f175,f114,f176,f186])).

fof(f186,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f118,f149])).

fof(f176,plain,(
    l1_pre_topc(sK1) ),
    inference(global_subsumption,[],[f108,f172])).

fof(f172,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f110,f127])).

fof(f110,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f175,plain,(
    v2_pre_topc(sK1) ),
    inference(global_subsumption,[],[f107,f108,f171])).

fof(f171,plain,
    ( v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f110,f138])).

fof(f109,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

fof(f114,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

fof(f5605,plain,
    ( ~ spl14_1057
    | ~ spl14_1059
    | spl14_793 ),
    inference(avatar_split_clause,[],[f5597,f4126,f5603,f5600])).

fof(f4126,plain,
    ( spl14_793
  <=> ~ r1_tarski(k2_xboole_0(sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_793])])).

fof(f5597,plain,
    ( ~ r1_tarski(sK9(sK2,sK4,sK7),sK7)
    | ~ r1_tarski(sK9(sK1,sK4,sK6),sK6)
    | ~ spl14_793 ),
    inference(resolution,[],[f4127,f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',t13_xboole_1)).

fof(f4127,plain,
    ( ~ r1_tarski(k2_xboole_0(sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7))
    | ~ spl14_793 ),
    inference(avatar_component_clause,[],[f4126])).

fof(f4128,plain,
    ( spl14_96
    | ~ spl14_161
    | ~ spl14_99
    | spl14_68
    | ~ spl14_101
    | spl14_78
    | ~ spl14_123
    | ~ spl14_401
    | ~ spl14_403
    | ~ spl14_405
    | ~ spl14_407
    | ~ spl14_409
    | ~ spl14_411
    | ~ spl14_413
    | ~ spl14_793
    | spl14_263 ),
    inference(avatar_split_clause,[],[f4122,f1401,f4126,f2208,f2205,f2202,f2199,f2196,f2193,f2190,f749,f448,f620,f413,f617,f944,f614])).

fof(f614,plain,
    ( spl14_96
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f944,plain,
    ( spl14_161
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_161])])).

fof(f617,plain,
    ( spl14_99
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_99])])).

fof(f413,plain,
    ( spl14_68
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f620,plain,
    ( spl14_101
  <=> ~ m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_101])])).

fof(f448,plain,
    ( spl14_78
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f749,plain,
    ( spl14_123
  <=> ~ m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_123])])).

fof(f2190,plain,
    ( spl14_401
  <=> ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_401])])).

fof(f2193,plain,
    ( spl14_403
  <=> ~ m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_403])])).

fof(f2196,plain,
    ( spl14_405
  <=> ~ m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_405])])).

fof(f2199,plain,
    ( spl14_407
  <=> ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_407])])).

fof(f2202,plain,
    ( spl14_409
  <=> ~ r2_hidden(sK4,sK9(sK1,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_409])])).

fof(f2205,plain,
    ( spl14_411
  <=> ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_411])])).

fof(f2208,plain,
    ( spl14_413
  <=> ~ r2_hidden(sK4,sK9(sK2,sK4,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_413])])).

fof(f1401,plain,
    ( spl14_263
  <=> ~ r1_tarski(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_263])])).

fof(f4122,plain,
    ( ~ r1_tarski(k2_xboole_0(sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7))
    | ~ r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ r2_hidden(sK4,sK9(sK1,sK4,sK6))
    | ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
    | ~ m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_263 ),
    inference(resolution,[],[f2344,f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(sK10(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tarski(sK10(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
                            & r2_hidden(X3,sK10(X0,X1,X2,X3,X4,X5))
                            & v3_pre_topc(sK10(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
                            & m1_subset_1(sK10(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f56,f97])).

fof(f97,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(X6,k2_xboole_0(X4,X5))
          & r2_hidden(X3,X6)
          & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK10(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
        & r2_hidden(X3,sK10(X0,X1,X2,X3,X4,X5))
        & v3_pre_topc(sK10(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                         => ~ ( ! [X6] :
                                  ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
                                 => ~ ( r1_tarski(X6,k2_xboole_0(X4,X5))
                                      & r2_hidden(X3,X6)
                                      & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2)) ) )
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X2)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',t19_tmap_1)).

fof(f2344,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),X0)
        | ~ r1_tarski(X0,k2_xboole_0(sK6,sK7)) )
    | ~ spl14_263 ),
    inference(resolution,[],[f1402,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t20_tmap_1.p',t1_xboole_1)).

fof(f1402,plain,
    ( ~ r1_tarski(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7))
    | ~ spl14_263 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f2319,plain,(
    spl14_413 ),
    inference(avatar_contradiction_clause,[],[f2317])).

fof(f2317,plain,
    ( $false
    | ~ spl14_413 ),
    inference(subsumption_resolution,[],[f517,f2209])).

fof(f2209,plain,
    ( ~ r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | ~ spl14_413 ),
    inference(avatar_component_clause,[],[f2208])).

fof(f517,plain,(
    r2_hidden(sK4,sK9(sK2,sK4,sK7)) ),
    inference(global_subsumption,[],[f185,f516])).

fof(f516,plain,
    ( r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f246,f188])).

fof(f246,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK7,sK2,X3)
      | r2_hidden(X3,sK9(sK2,X3,sK7))
      | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f111,f183,f184,f238])).

fof(f238,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK7,sK2,X3)
      | r2_hidden(X3,sK9(sK2,X3,sK7))
      | ~ m1_subset_1(X3,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f2297,plain,(
    spl14_411 ),
    inference(avatar_contradiction_clause,[],[f2296])).

fof(f2296,plain,
    ( $false
    | ~ spl14_411 ),
    inference(subsumption_resolution,[],[f513,f2206])).

fof(f2206,plain,
    ( ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ spl14_411 ),
    inference(avatar_component_clause,[],[f2205])).

fof(f513,plain,(
    v3_pre_topc(sK9(sK2,sK4,sK7),sK2) ),
    inference(global_subsumption,[],[f185,f512])).

fof(f512,plain,
    ( v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f244,f188])).

fof(f244,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK7,sK2,X1)
      | v3_pre_topc(sK9(sK2,X1,sK7),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f111,f183,f184,f236])).

fof(f236,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK7,sK2,X1)
      | v3_pre_topc(sK9(sK2,X1,sK7),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v3_pre_topc(sK9(X0,X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f2281,plain,(
    spl14_409 ),
    inference(avatar_contradiction_clause,[],[f2279])).

fof(f2279,plain,
    ( $false
    | ~ spl14_409 ),
    inference(subsumption_resolution,[],[f511,f2203])).

fof(f2203,plain,
    ( ~ r2_hidden(sK4,sK9(sK1,sK4,sK6))
    | ~ spl14_409 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f511,plain,(
    r2_hidden(sK4,sK9(sK1,sK4,sK6)) ),
    inference(global_subsumption,[],[f114,f510])).

fof(f510,plain,
    ( r2_hidden(sK4,sK9(sK1,sK4,sK6))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[],[f203,f118])).

fof(f203,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK6,sK1,X3)
      | r2_hidden(X3,sK9(sK1,X3,sK6))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f109,f175,f176,f195])).

fof(f195,plain,(
    ! [X3] :
      ( ~ m1_connsp_2(sK6,sK1,X3)
      | r2_hidden(X3,sK9(sK1,X3,sK6))
      | ~ m1_subset_1(X3,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f187,f132])).

fof(f2261,plain,(
    spl14_407 ),
    inference(avatar_contradiction_clause,[],[f2260])).

fof(f2260,plain,
    ( $false
    | ~ spl14_407 ),
    inference(subsumption_resolution,[],[f401,f2200])).

fof(f2200,plain,
    ( ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
    | ~ spl14_407 ),
    inference(avatar_component_clause,[],[f2199])).

fof(f401,plain,(
    v3_pre_topc(sK9(sK1,sK4,sK6),sK1) ),
    inference(global_subsumption,[],[f114,f400])).

fof(f400,plain,
    ( v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[],[f201,f118])).

fof(f201,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK6,sK1,X1)
      | v3_pre_topc(sK9(sK1,X1,sK6),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f109,f175,f176,f193])).

fof(f193,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK6,sK1,X1)
      | v3_pre_topc(sK9(sK1,X1,sK6),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f187,f130])).

fof(f2243,plain,(
    spl14_405 ),
    inference(avatar_contradiction_clause,[],[f2242])).

fof(f2242,plain,
    ( $false
    | ~ spl14_405 ),
    inference(subsumption_resolution,[],[f522,f2197])).

fof(f2197,plain,
    ( ~ m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_405 ),
    inference(avatar_component_clause,[],[f2196])).

fof(f522,plain,(
    m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f185,f521])).

fof(f521,plain,
    ( m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f243,f188])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK7,sK2,X0)
      | m1_subset_1(sK9(sK2,X0,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f111,f183,f184,f235])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK7,sK2,X0)
      | m1_subset_1(sK9(sK2,X0,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f2226,plain,(
    spl14_403 ),
    inference(avatar_contradiction_clause,[],[f2225])).

fof(f2225,plain,
    ( $false
    | ~ spl14_403 ),
    inference(subsumption_resolution,[],[f520,f2194])).

fof(f2194,plain,
    ( ~ m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl14_403 ),
    inference(avatar_component_clause,[],[f2193])).

fof(f520,plain,(
    m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_subsumption,[],[f114,f519])).

fof(f519,plain,
    ( m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[],[f200,f118])).

fof(f200,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK6,sK1,X0)
      | m1_subset_1(sK9(sK1,X0,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f109,f175,f176,f192])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK6,sK1,X0)
      | m1_subset_1(sK9(sK1,X0,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f187,f129])).

fof(f2219,plain,(
    spl14_401 ),
    inference(avatar_contradiction_clause,[],[f2218])).

fof(f2218,plain,
    ( $false
    | ~ spl14_401 ),
    inference(subsumption_resolution,[],[f191,f2191])).

fof(f2191,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl14_401 ),
    inference(avatar_component_clause,[],[f2190])).

fof(f191,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f166,f165])).

fof(f166,plain,(
    m1_subset_1(sK5,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f113,f117])).

fof(f113,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f90])).

fof(f2210,plain,
    ( spl14_96
    | ~ spl14_161
    | ~ spl14_99
    | spl14_68
    | ~ spl14_101
    | spl14_78
    | ~ spl14_123
    | ~ spl14_401
    | ~ spl14_403
    | ~ spl14_405
    | ~ spl14_407
    | ~ spl14_409
    | ~ spl14_411
    | ~ spl14_413
    | spl14_261 ),
    inference(avatar_split_clause,[],[f2187,f1398,f2208,f2205,f2202,f2199,f2196,f2193,f2190,f749,f448,f620,f413,f617,f944,f614])).

fof(f1398,plain,
    ( spl14_261
  <=> ~ r2_hidden(sK4,sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_261])])).

fof(f2187,plain,
    ( ~ r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ r2_hidden(sK4,sK9(sK1,sK4,sK6))
    | ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
    | ~ m1_subset_1(sK9(sK2,sK4,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK9(sK1,sK4,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_261 ),
    inference(resolution,[],[f1399,f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X3,sK10(X0,X1,X2,X3,X4,X5))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f1399,plain,
    ( ~ r2_hidden(sK4,sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)))
    | ~ spl14_261 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1403,plain,
    ( ~ spl14_261
    | ~ spl14_263 ),
    inference(avatar_split_clause,[],[f1396,f1401,f1398])).

fof(f1396,plain,
    ( ~ r1_tarski(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7))
    | ~ r2_hidden(sK4,sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7))) ),
    inference(global_subsumption,[],[f1128,f1387])).

fof(f1387,plain,
    ( ~ r1_tarski(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k2_xboole_0(sK6,sK7))
    | ~ v3_pre_topc(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k1_tsep_1(sK0,sK1,sK2))
    | ~ r2_hidden(sK4,sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7))) ),
    inference(resolution,[],[f1142,f223])).

fof(f223,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
      | ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
      | ~ r2_hidden(sK4,X8) ) ),
    inference(forward_demodulation,[],[f164,f165])).

fof(f164,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ r2_hidden(sK5,X8)
      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(definition_unfolding,[],[f120,f117])).

fof(f120,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ r2_hidden(sK3,X8)
      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f1142,plain,(
    m1_subset_1(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    inference(global_subsumption,[],[f513,f517,f1140])).

fof(f1140,plain,
    ( ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | m1_subset_1(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f568,f522])).

fof(f568,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X0,sK2)
      | ~ r2_hidden(sK4,X0)
      | m1_subset_1(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(global_subsumption,[],[f401,f511,f558])).

fof(f558,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ r2_hidden(sK4,sK9(sK1,sK4,sK6))
      | ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4,X0)
      | m1_subset_1(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(resolution,[],[f520,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK2)
      | ~ r2_hidden(sK4,X1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4,X0)
      | m1_subset_1(sK10(sK0,sK1,sK2,sK4,X1,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(global_subsumption,[],[f106,f107,f108,f109,f111,f110,f112,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,X0)
      | ~ v3_pre_topc(X0,sK2)
      | ~ r2_hidden(sK4,X1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK10(sK0,sK1,sK2,sK4,X1,X0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f191,f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK10(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f106,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f90])).

fof(f1128,plain,(
    v3_pre_topc(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(global_subsumption,[],[f513,f517,f1126])).

fof(f1126,plain,
    ( ~ v3_pre_topc(sK9(sK2,sK4,sK7),sK2)
    | ~ r2_hidden(sK4,sK9(sK2,sK4,sK7))
    | v3_pre_topc(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),sK9(sK2,sK4,sK7)),k1_tsep_1(sK0,sK1,sK2)) ),
    inference(resolution,[],[f569,f522])).

fof(f569,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_pre_topc(X1,sK2)
      | ~ r2_hidden(sK4,X1)
      | v3_pre_topc(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),X1),k1_tsep_1(sK0,sK1,sK2)) ) ),
    inference(global_subsumption,[],[f401,f511,f559])).

fof(f559,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK2)
      | ~ r2_hidden(sK4,sK9(sK1,sK4,sK6))
      | ~ v3_pre_topc(sK9(sK1,sK4,sK6),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4,X1)
      | v3_pre_topc(sK10(sK0,sK1,sK2,sK4,sK9(sK1,sK4,sK6),X1),k1_tsep_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f520,f222])).

fof(f222,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X2,sK2)
      | ~ r2_hidden(sK4,X3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4,X2)
      | v3_pre_topc(sK10(sK0,sK1,sK2,sK4,X3,X2),k1_tsep_1(sK0,sK1,sK2)) ) ),
    inference(global_subsumption,[],[f106,f107,f108,f109,f111,f110,f112,f220])).

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4,X2)
      | ~ v3_pre_topc(X2,sK2)
      | ~ r2_hidden(sK4,X3)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(sK10(sK0,sK1,sK2,sK4,X3,X2),k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f191,f135])).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(sK10(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f959,plain,(
    spl14_161 ),
    inference(avatar_contradiction_clause,[],[f958])).

fof(f958,plain,
    ( $false
    | ~ spl14_161 ),
    inference(subsumption_resolution,[],[f107,f945])).

fof(f945,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl14_161 ),
    inference(avatar_component_clause,[],[f944])).

fof(f802,plain,(
    ~ spl14_78 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | ~ spl14_78 ),
    inference(subsumption_resolution,[],[f111,f449])).

fof(f449,plain,
    ( v2_struct_0(sK2)
    | ~ spl14_78 ),
    inference(avatar_component_clause,[],[f448])).

fof(f763,plain,(
    spl14_123 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | ~ spl14_123 ),
    inference(subsumption_resolution,[],[f112,f750])).

fof(f750,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl14_123 ),
    inference(avatar_component_clause,[],[f749])).

fof(f729,plain,(
    ~ spl14_96 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | ~ spl14_96 ),
    inference(subsumption_resolution,[],[f106,f615])).

fof(f615,plain,
    ( v2_struct_0(sK0)
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f614])).

fof(f689,plain,(
    ~ spl14_68 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl14_68 ),
    inference(subsumption_resolution,[],[f109,f414])).

fof(f414,plain,
    ( v2_struct_0(sK1)
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f413])).

fof(f665,plain,(
    spl14_101 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl14_101 ),
    inference(subsumption_resolution,[],[f110,f621])).

fof(f621,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl14_101 ),
    inference(avatar_component_clause,[],[f620])).

fof(f651,plain,(
    spl14_99 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl14_99 ),
    inference(subsumption_resolution,[],[f108,f618])).

fof(f618,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl14_99 ),
    inference(avatar_component_clause,[],[f617])).
%------------------------------------------------------------------------------
