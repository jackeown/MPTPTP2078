%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  233 (2011 expanded)
%              Number of leaves         :   32 ( 864 expanded)
%              Depth                    :   31
%              Number of atoms          : 1068 (29429 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f118,f129,f143,f154,f310,f317,f322,f324,f339,f356,f361,f363,f375,f404,f407,f418])).

fof(f418,plain,
    ( ~ spl13_3
    | ~ spl13_6
    | spl13_15 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | ~ spl13_3
    | ~ spl13_6
    | spl13_15 ),
    inference(subsumption_resolution,[],[f416,f308])).

fof(f308,plain,
    ( ~ sP2(sK12,sK10,sK8,sK11,sK9,sK7)
    | spl13_15 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl13_15
  <=> sP2(sK12,sK10,sK8,sK11,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f416,plain,
    ( sP2(sK12,sK10,sK8,sK11,sK9,sK7)
    | ~ spl13_3
    | ~ spl13_6 ),
    inference(resolution,[],[f410,f408])).

fof(f408,plain,
    ( r1_binop_1(sK8,sK10,sK12)
    | ~ spl13_6 ),
    inference(resolution,[],[f138,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r1_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ~ r2_binop_1(X2,X1,X0)
        | ~ r1_binop_1(X2,X1,X0) )
      & ( ( r2_binop_1(X2,X1,X0)
          & r1_binop_1(X2,X1,X0) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ~ r2_binop_1(X0,X1,X2)
        | ~ r1_binop_1(X0,X1,X2) )
      & ( ( r2_binop_1(X0,X1,X2)
          & r1_binop_1(X0,X1,X2) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ~ r2_binop_1(X0,X1,X2)
        | ~ r1_binop_1(X0,X1,X2) )
      & ( ( r2_binop_1(X0,X1,X2)
          & r1_binop_1(X0,X1,X2) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( sP4(X2,X1,X0)
    <=> ( r2_binop_1(X0,X1,X2)
        & r1_binop_1(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f138,plain,
    ( sP4(sK12,sK10,sK8)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl13_6
  <=> sP4(sK12,sK10,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f410,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_binop_1(X0,X1,X2)
        | sP2(X2,X1,X0,sK11,sK9,sK7) )
    | ~ spl13_3 ),
    inference(resolution,[],[f365,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_binop_1(X5,X4,X3)
      | ~ r1_binop_1(X2,X1,X0)
      | sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP2(X0,X1,X2,X3,X4,X5)
        | ~ r1_binop_1(X2,X1,X0)
        | ~ r1_binop_1(X5,X4,X3) )
      & ( ( r1_binop_1(X2,X1,X0)
          & r1_binop_1(X5,X4,X3) )
        | ~ sP2(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( ( sP2(X5,X3,X1,X4,X2,X0)
        | ~ r1_binop_1(X1,X3,X5)
        | ~ r1_binop_1(X0,X2,X4) )
      & ( ( r1_binop_1(X1,X3,X5)
          & r1_binop_1(X0,X2,X4) )
        | ~ sP2(X5,X3,X1,X4,X2,X0) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( ( sP2(X5,X3,X1,X4,X2,X0)
        | ~ r1_binop_1(X1,X3,X5)
        | ~ r1_binop_1(X0,X2,X4) )
      & ( ( r1_binop_1(X1,X3,X5)
          & r1_binop_1(X0,X2,X4) )
        | ~ sP2(X5,X3,X1,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( sP2(X5,X3,X1,X4,X2,X0)
    <=> ( r1_binop_1(X1,X3,X5)
        & r1_binop_1(X0,X2,X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f365,plain,
    ( r1_binop_1(sK7,sK9,sK11)
    | ~ spl13_3 ),
    inference(resolution,[],[f117,f83])).

fof(f117,plain,
    ( sP4(sK11,sK9,sK7)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl13_3
  <=> sP4(sK11,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f407,plain,
    ( spl13_2
    | spl13_7 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl13_2
    | spl13_7 ),
    inference(subsumption_resolution,[],[f142,f405])).

fof(f405,plain,
    ( r3_binop_1(sK8,sK10,sK12)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f67,f106])).

fof(f106,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl13_2
  <=> r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f67,plain,
    ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | r3_binop_1(sK8,sK10,sK12) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ r3_binop_1(sK8,sK10,sK12)
      | ~ r3_binop_1(sK7,sK9,sK11) )
    & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
      | ( r3_binop_1(sK8,sK10,sK12)
        & r3_binop_1(sK7,sK9,sK11) ) )
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
    & v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    & v1_funct_1(sK12)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
    & v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,sK8)
    & m1_subset_1(sK9,sK7)
    & ~ v1_xboole_0(sK8)
    & ~ v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f32,f38,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ~ r3_binop_1(X1,X3,X5)
                              | ~ r3_binop_1(X0,X2,X4) )
                            & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                              | ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) ) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,X1) )
                & m1_subset_1(X2,X0) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(sK7,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(sK7,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
                      & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,sK7) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5))
                          | ~ r3_binop_1(X1,X3,X5)
                          | ~ r3_binop_1(sK7,X2,X4) )
                        & ( r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5))
                          | ( r3_binop_1(X1,X3,X5)
                            & r3_binop_1(sK7,X2,X4) ) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
                    & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,X1) )
            & m1_subset_1(X2,sK7) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5))
                        | ~ r3_binop_1(sK8,X3,X5)
                        | ~ r3_binop_1(sK7,X2,X4) )
                      & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5))
                        | ( r3_binop_1(sK8,X3,X5)
                          & r3_binop_1(sK7,X2,X4) ) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
                      & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
                  & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,sK8) )
          & m1_subset_1(X2,sK7) )
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5))
                      | ~ r3_binop_1(sK8,X3,X5)
                      | ~ r3_binop_1(sK7,X2,X4) )
                    & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5))
                      | ( r3_binop_1(sK8,X3,X5)
                        & r3_binop_1(sK7,X2,X4) ) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
                    & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
                & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
                & v1_funct_1(X4) )
            & m1_subset_1(X3,sK8) )
        & m1_subset_1(X2,sK7) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5))
                    | ~ r3_binop_1(sK8,X3,X5)
                    | ~ r3_binop_1(sK7,sK9,X4) )
                  & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5))
                    | ( r3_binop_1(sK8,X3,X5)
                      & r3_binop_1(sK7,sK9,X4) ) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
                  & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
              & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
              & v1_funct_1(X4) )
          & m1_subset_1(X3,sK8) )
      & m1_subset_1(sK9,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5))
                  | ~ r3_binop_1(sK8,X3,X5)
                  | ~ r3_binop_1(sK7,sK9,X4) )
                & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5))
                  | ( r3_binop_1(sK8,X3,X5)
                    & r3_binop_1(sK7,sK9,X4) ) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
                & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
            & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,sK8) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5))
                | ~ r3_binop_1(sK8,sK10,X5)
                | ~ r3_binop_1(sK7,sK9,X4) )
              & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5))
                | ( r3_binop_1(sK8,sK10,X5)
                  & r3_binop_1(sK7,sK9,X4) ) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
              & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
          & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
          & v1_funct_1(X4) )
      & m1_subset_1(sK10,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5))
              | ~ r3_binop_1(sK8,sK10,X5)
              | ~ r3_binop_1(sK7,sK9,X4) )
            & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5))
              | ( r3_binop_1(sK8,sK10,X5)
                & r3_binop_1(sK7,sK9,X4) ) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
            & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
        & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5))
            | ~ r3_binop_1(sK8,sK10,X5)
            | ~ r3_binop_1(sK7,sK9,sK11) )
          & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5))
            | ( r3_binop_1(sK8,sK10,X5)
              & r3_binop_1(sK7,sK9,sK11) ) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
          & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
          & v1_funct_1(X5) )
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))
      & v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X5] :
        ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5))
          | ~ r3_binop_1(sK8,sK10,X5)
          | ~ r3_binop_1(sK7,sK9,sK11) )
        & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5))
          | ( r3_binop_1(sK8,sK10,X5)
            & r3_binop_1(sK7,sK9,sK11) ) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
        & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8)
        & v1_funct_1(X5) )
   => ( ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
        | ~ r3_binop_1(sK8,sK10,sK12)
        | ~ r3_binop_1(sK7,sK9,sK11) )
      & ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
        | ( r3_binop_1(sK8,sK10,sK12)
          & r3_binop_1(sK7,sK9,sK11) ) )
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
      & v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
      & v1_funct_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ~ r3_binop_1(X1,X3,X5)
                            | ~ r3_binop_1(X0,X2,X4) )
                          & ( r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
                            | ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) ) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,X1) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X1)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                          & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                              & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                              & v1_funct_1(X5) )
                           => ( ( r3_binop_1(X1,X3,X5)
                                & r3_binop_1(X0,X2,X4) )
                            <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r3_binop_1(X1,X3,X5)
                              & r3_binop_1(X0,X2,X4) )
                          <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_filter_1)).

fof(f142,plain,
    ( ~ r3_binop_1(sK8,sK10,sK12)
    | spl13_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl13_7
  <=> r3_binop_1(sK8,sK10,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f404,plain,
    ( spl13_2
    | ~ spl13_3
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_15
    | ~ spl13_16 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl13_2
    | ~ spl13_3
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_15
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f402,f368])).

fof(f368,plain,
    ( r2_binop_1(sK8,sK10,sK12)
    | ~ spl13_6 ),
    inference(resolution,[],[f138,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r2_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f402,plain,
    ( ~ r2_binop_1(sK8,sK10,sK12)
    | spl13_2
    | ~ spl13_3
    | ~ spl13_14
    | ~ spl13_15
    | ~ spl13_16 ),
    inference(resolution,[],[f401,f370])).

fof(f370,plain,
    ( ! [X2,X0,X1] :
        ( sP0(X2,X1,X0,sK11,sK9,sK7)
        | ~ r2_binop_1(X0,X1,X2) )
    | ~ spl13_3 ),
    inference(resolution,[],[f366,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_binop_1(X5,X4,X3)
      | ~ r2_binop_1(X2,X1,X0)
      | sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ~ r2_binop_1(X2,X1,X0)
        | ~ r2_binop_1(X5,X4,X3) )
      & ( ( r2_binop_1(X2,X1,X0)
          & r2_binop_1(X5,X4,X3) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( ( sP0(X5,X3,X1,X4,X2,X0)
        | ~ r2_binop_1(X1,X3,X5)
        | ~ r2_binop_1(X0,X2,X4) )
      & ( ( r2_binop_1(X1,X3,X5)
          & r2_binop_1(X0,X2,X4) )
        | ~ sP0(X5,X3,X1,X4,X2,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( ( sP0(X5,X3,X1,X4,X2,X0)
        | ~ r2_binop_1(X1,X3,X5)
        | ~ r2_binop_1(X0,X2,X4) )
      & ( ( r2_binop_1(X1,X3,X5)
          & r2_binop_1(X0,X2,X4) )
        | ~ sP0(X5,X3,X1,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X5,X3,X1,X4,X2,X0] :
      ( sP0(X5,X3,X1,X4,X2,X0)
    <=> ( r2_binop_1(X1,X3,X5)
        & r2_binop_1(X0,X2,X4) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f366,plain,
    ( r2_binop_1(sK7,sK9,sK11)
    | ~ spl13_3 ),
    inference(resolution,[],[f117,f84])).

fof(f401,plain,
    ( ~ sP0(sK12,sK10,sK8,sK11,sK9,sK7)
    | spl13_2
    | ~ spl13_14
    | ~ spl13_15
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f357,f400])).

fof(f400,plain,
    ( ~ r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | spl13_2
    | ~ spl13_14
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f396,f379])).

fof(f379,plain,
    ( r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_14
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f318,f309])).

fof(f309,plain,
    ( sP2(sK12,sK10,sK8,sK11,sK9,sK7)
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f307])).

fof(f318,plain,
    ( ~ sP2(sK12,sK10,sK8,sK11,sK9,sK7)
    | r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_14 ),
    inference(resolution,[],[f304,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3,X4,X5)
      | ~ sP2(X0,X4,X2,X1,X5,X3)
      | r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( sP2(X0,X4,X2,X1,X5,X3)
          | ~ r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) )
        & ( r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))
          | ~ sP2(X0,X4,X2,X1,X5,X3) ) )
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X5,X4,X1,X0,X3,X2] :
      ( ( ( sP2(X5,X3,X1,X4,X2,X0)
          | ~ r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
        & ( r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
          | ~ sP2(X5,X3,X1,X4,X2,X0) ) )
      | ~ sP3(X5,X4,X1,X0,X3,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X5,X4,X1,X0,X3,X2] :
      ( ( sP2(X5,X3,X1,X4,X2,X0)
      <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
      | ~ sP3(X5,X4,X1,X0,X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f304,plain,
    ( sP3(sK12,sK11,sK8,sK7,sK10,sK9)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl13_14
  <=> sP3(sK12,sK11,sK8,sK7,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f396,plain,
    ( ~ r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | spl13_2 ),
    inference(resolution,[],[f395,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ r2_binop_1(X2,X1,X0)
      | ~ r1_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f395,plain,
    ( ~ sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8))
    | spl13_2 ),
    inference(subsumption_resolution,[],[f294,f106])).

fof(f294,plain,
    ( ~ sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8))
    | r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) ),
    inference(resolution,[],[f292,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | r3_binop_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_binop_1(X0,X1,X2)
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r3_binop_1(X0,X1,X2) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_binop_1(X0,X1,X2)
      <=> sP4(X2,X1,X0) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f292,plain,(
    sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) ),
    inference(resolution,[],[f291,f58])).

fof(f58,plain,(
    m1_subset_1(sK9,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f291,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK7)
      | sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) ) ),
    inference(resolution,[],[f290,f59])).

fof(f59,plain,(
    m1_subset_1(sK10,sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK8)
      | sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ m1_subset_1(X0,sK7) ) ),
    inference(subsumption_resolution,[],[f289,f56])).

fof(f56,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f289,plain,(
    ! [X0,X1] :
      ( sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ m1_subset_1(X1,sK8)
      | ~ m1_subset_1(X0,sK7)
      | v1_xboole_0(sK7) ) ),
    inference(subsumption_resolution,[],[f288,f57])).

fof(f57,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f288,plain,(
    ! [X0,X1] :
      ( sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ m1_subset_1(X1,sK8)
      | ~ m1_subset_1(X0,sK7)
      | v1_xboole_0(sK8)
      | v1_xboole_0(sK7) ) ),
    inference(resolution,[],[f287,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_domain_1)).

fof(f287,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(sK7,sK8))
      | sP5(k2_zfmisc_1(sK7,sK8),X0,k6_filter_1(sK7,sK8,sK11,sK12)) ) ),
    inference(subsumption_resolution,[],[f286,f172])).

fof(f172,plain,(
    v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[],[f170,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | v1_funct_2(k6_filter_1(X1,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X1,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0))))
        & v1_funct_2(k6_filter_1(X1,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0))
        & v1_funct_1(k6_filter_1(X1,X0,X3,X2)) )
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X3,X2] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ sP6(X1,X0,X3,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X3,X2] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ sP6(X1,X0,X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f170,plain,(
    sP6(sK8,sK7,sK12,sK11) ),
    inference(subsumption_resolution,[],[f169,f64])).

fof(f64,plain,(
    v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) ),
    inference(cnf_transformation,[],[f39])).

fof(f169,plain,
    ( ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | sP6(sK8,sK7,sK12,sK11) ),
    inference(resolution,[],[f158,f65])).

fof(f65,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) ),
    inference(cnf_transformation,[],[f39])).

fof(f158,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(sK12,k2_zfmisc_1(X1,X1),X1)
      | sP6(X1,sK7,sK12,sK11) ) ),
    inference(resolution,[],[f156,f63])).

fof(f63,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f39])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | sP6(X1,sK7,X0,sK11) ) ),
    inference(subsumption_resolution,[],[f155,f61])).

fof(f61,plain,(
    v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
      | sP6(X1,sK7,X0,sK11) ) ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(X2,X2),X2)
      | sP6(X1,X2,X0,sK11) ) ),
    inference(resolution,[],[f60,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | sP6(X1,X0,X3,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( sP6(X1,X0,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f19,f29])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).

fof(f60,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f39])).

fof(f286,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))
      | sP5(k2_zfmisc_1(sK7,sK8),X0,k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ m1_subset_1(X0,k2_zfmisc_1(sK7,sK8)) ) ),
    inference(resolution,[],[f176,f173])).

fof(f173,plain,(
    m1_subset_1(k6_filter_1(sK7,sK8,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8)))) ),
    inference(resolution,[],[f170,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | m1_subset_1(k6_filter_1(X1,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0)))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f176,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(k6_filter_1(sK7,sK8,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4)))
      | ~ v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(X4,X4),X4)
      | sP5(X4,X5,k6_filter_1(sK7,sK8,sK11,sK12))
      | ~ m1_subset_1(X5,X4) ) ),
    inference(resolution,[],[f171,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | sP5(X0,X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP5(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_folding,[],[f15,f27,f26])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

fof(f171,plain,(
    v1_funct_1(k6_filter_1(sK7,sK8,sK11,sK12)) ),
    inference(resolution,[],[f170,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | v1_funct_1(k6_filter_1(X1,X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f357,plain,
    ( ~ sP0(sK12,sK10,sK8,sK11,sK9,sK7)
    | r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_16 ),
    inference(resolution,[],[f333,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5)
      | ~ sP0(X0,X4,X2,X1,X5,X3)
      | r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( sP0(X0,X4,X2,X1,X5,X3)
          | ~ r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) )
        & ( r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))
          | ~ sP0(X0,X4,X2,X1,X5,X3) ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X5,X4,X1,X0,X3,X2] :
      ( ( ( sP0(X5,X3,X1,X4,X2,X0)
          | ~ r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
        & ( r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))
          | ~ sP0(X5,X3,X1,X4,X2,X0) ) )
      | ~ sP1(X5,X4,X1,X0,X3,X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X5,X4,X1,X0,X3,X2] :
      ( ( sP0(X5,X3,X1,X4,X2,X0)
      <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
      | ~ sP1(X5,X4,X1,X0,X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f333,plain,
    ( sP1(sK12,sK11,sK8,sK7,sK10,sK9)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl13_16
  <=> sP1(sK12,sK11,sK8,sK7,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f375,plain,
    ( ~ spl13_1
    | ~ spl13_2
    | ~ spl13_7 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f373,f103])).

fof(f103,plain,
    ( r3_binop_1(sK7,sK9,sK11)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl13_1
  <=> r3_binop_1(sK7,sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f373,plain,
    ( ~ r3_binop_1(sK7,sK9,sK11)
    | ~ spl13_2
    | ~ spl13_7 ),
    inference(subsumption_resolution,[],[f364,f141])).

fof(f141,plain,
    ( r3_binop_1(sK8,sK10,sK12)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f364,plain,
    ( ~ r3_binop_1(sK8,sK10,sK12)
    | ~ r3_binop_1(sK7,sK9,sK11)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f68,f107])).

fof(f107,plain,
    ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f68,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ r3_binop_1(sK8,sK10,sK12)
    | ~ r3_binop_1(sK7,sK9,sK11) ),
    inference(cnf_transformation,[],[f39])).

fof(f363,plain,
    ( spl13_9
    | ~ spl13_17 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl13_9
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f359,f153])).

fof(f153,plain,
    ( ~ r2_binop_1(sK8,sK10,sK12)
    | spl13_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl13_9
  <=> r2_binop_1(sK8,sK10,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f359,plain,
    ( r2_binop_1(sK8,sK10,sK12)
    | ~ spl13_17 ),
    inference(resolution,[],[f338,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | r2_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f338,plain,
    ( sP0(sK12,sK10,sK8,sK11,sK9,sK7)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl13_17
  <=> sP0(sK12,sK10,sK8,sK11,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f361,plain,
    ( spl13_5
    | ~ spl13_17 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl13_5
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f358,f128])).

fof(f128,plain,
    ( ~ r2_binop_1(sK7,sK9,sK11)
    | spl13_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl13_5
  <=> r2_binop_1(sK7,sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f358,plain,
    ( r2_binop_1(sK7,sK9,sK11)
    | ~ spl13_17 ),
    inference(resolution,[],[f338,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | r2_binop_1(X5,X4,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f356,plain,(
    spl13_16 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl13_16 ),
    inference(subsumption_resolution,[],[f354,f57])).

fof(f354,plain,
    ( v1_xboole_0(sK8)
    | spl13_16 ),
    inference(subsumption_resolution,[],[f353,f64])).

fof(f353,plain,
    ( ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_16 ),
    inference(subsumption_resolution,[],[f352,f59])).

fof(f352,plain,
    ( ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_16 ),
    inference(subsumption_resolution,[],[f351,f63])).

fof(f351,plain,
    ( ~ v1_funct_1(sK12)
    | ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_16 ),
    inference(subsumption_resolution,[],[f350,f65])).

fof(f350,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
    | ~ v1_funct_1(sK12)
    | ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_16 ),
    inference(resolution,[],[f348,f334])).

fof(f334,plain,
    ( ~ sP1(sK12,sK11,sK8,sK7,sK10,sK9)
    | spl13_16 ),
    inference(avatar_component_clause,[],[f332])).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,sK11,X1,sK7,X2,sK9)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f342,f58])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,sK7)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | sP1(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f341,f56])).

fof(f341,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | sP1(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,sK7)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK7) ) ),
    inference(subsumption_resolution,[],[f340,f61])).

fof(f340,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
      | sP1(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,sK7)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK7) ) ),
    inference(resolution,[],[f95,f62])).

fof(f95,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X12),X12)))
      | ~ v1_funct_2(X10,k2_zfmisc_1(X11,X11),X11)
      | ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(X12,X12),X12)
      | sP1(X10,sK11,X11,X12,X13,X14)
      | ~ m1_subset_1(X13,X11)
      | ~ m1_subset_1(X14,X12)
      | v1_xboole_0(X11)
      | v1_xboole_0(X12) ) ),
    inference(resolution,[],[f60,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | sP1(X5,X4,X1,X0,X3,X2)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( sP1(X5,X4,X1,X0,X3,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f11,f21,f20])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r2_binop_1(X1,X3,X5)
                              & r2_binop_1(X0,X2,X4) )
                          <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_filter_1)).

fof(f339,plain,
    ( ~ spl13_16
    | spl13_17
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f300,f105,f336,f332])).

fof(f300,plain,
    ( sP0(sK12,sK10,sK8,sK11,sK9,sK7)
    | ~ sP1(sK12,sK11,sK8,sK7,sK10,sK9)
    | ~ spl13_2 ),
    inference(resolution,[],[f297,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))
      | sP0(X0,X4,X2,X1,X5,X3)
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f297,plain,
    ( r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_2 ),
    inference(resolution,[],[f295,f84])).

fof(f295,plain,
    ( sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8))
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f293,f107])).

fof(f293,plain,
    ( ~ r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8)) ),
    inference(resolution,[],[f292,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f324,plain,
    ( spl13_8
    | ~ spl13_15 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl13_8
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f320,f149])).

fof(f149,plain,
    ( ~ r1_binop_1(sK8,sK10,sK12)
    | spl13_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl13_8
  <=> r1_binop_1(sK8,sK10,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f320,plain,
    ( r1_binop_1(sK8,sK10,sK12)
    | ~ spl13_15 ),
    inference(resolution,[],[f309,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5)
      | r1_binop_1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f322,plain,
    ( spl13_4
    | ~ spl13_15 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl13_4
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f319,f124])).

fof(f124,plain,
    ( ~ r1_binop_1(sK7,sK9,sK11)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl13_4
  <=> r1_binop_1(sK7,sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f319,plain,
    ( r1_binop_1(sK7,sK9,sK11)
    | ~ spl13_15 ),
    inference(resolution,[],[f309,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5)
      | r1_binop_1(X5,X4,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f317,plain,(
    spl13_14 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl13_14 ),
    inference(subsumption_resolution,[],[f315,f57])).

fof(f315,plain,
    ( v1_xboole_0(sK8)
    | spl13_14 ),
    inference(subsumption_resolution,[],[f314,f64])).

fof(f314,plain,
    ( ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_14 ),
    inference(subsumption_resolution,[],[f313,f59])).

fof(f313,plain,
    ( ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_14 ),
    inference(subsumption_resolution,[],[f312,f63])).

fof(f312,plain,
    ( ~ v1_funct_1(sK12)
    | ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_14 ),
    inference(subsumption_resolution,[],[f311,f65])).

fof(f311,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
    | ~ v1_funct_1(sK12)
    | ~ m1_subset_1(sK10,sK8)
    | ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
    | v1_xboole_0(sK8)
    | spl13_14 ),
    inference(resolution,[],[f305,f284])).

fof(f284,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,sK11,X1,sK7,X2,sK9)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f273,f58])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,sK7)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | sP3(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f272,f56])).

fof(f272,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | sP3(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,sK7)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK7) ) ),
    inference(subsumption_resolution,[],[f271,f61])).

fof(f271,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
      | sP3(X0,sK11,X1,sK7,X2,X3)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X3,sK7)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK7) ) ),
    inference(resolution,[],[f94,f62])).

fof(f94,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X6,X6),X6)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,X6),X6)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(X7,X7),X7)
      | sP3(X5,sK11,X6,X7,X8,X9)
      | ~ m1_subset_1(X8,X6)
      | ~ m1_subset_1(X9,X7)
      | v1_xboole_0(X6)
      | v1_xboole_0(X7) ) ),
    inference(resolution,[],[f60,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
      | sP3(X5,X4,X1,X0,X3,X2)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( sP3(X5,X4,X1,X0,X3,X2)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f13,f24,f23])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,X1) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                        & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r1_binop_1(X1,X3,X5)
                              & r1_binop_1(X0,X2,X4) )
                          <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_filter_1)).

fof(f305,plain,
    ( ~ sP3(sK12,sK11,sK8,sK7,sK10,sK9)
    | spl13_14 ),
    inference(avatar_component_clause,[],[f303])).

fof(f310,plain,
    ( ~ spl13_14
    | spl13_15
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f298,f105,f307,f303])).

fof(f298,plain,
    ( sP2(sK12,sK10,sK8,sK11,sK9,sK7)
    | ~ sP3(sK12,sK11,sK8,sK7,sK10,sK9)
    | ~ spl13_2 ),
    inference(resolution,[],[f296,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))
      | sP2(X0,X4,X2,X1,X5,X3)
      | ~ sP3(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f296,plain,
    ( r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | ~ spl13_2 ),
    inference(resolution,[],[f295,f83])).

fof(f154,plain,
    ( ~ spl13_8
    | ~ spl13_9
    | spl13_7 ),
    inference(avatar_split_clause,[],[f145,f140,f151,f147])).

fof(f145,plain,
    ( ~ r2_binop_1(sK8,sK10,sK12)
    | ~ r1_binop_1(sK8,sK10,sK12)
    | spl13_7 ),
    inference(resolution,[],[f144,f85])).

fof(f144,plain,
    ( ~ sP4(sK12,sK10,sK8)
    | spl13_7 ),
    inference(subsumption_resolution,[],[f134,f142])).

fof(f134,plain,
    ( ~ sP4(sK12,sK10,sK8)
    | r3_binop_1(sK8,sK10,sK12) ),
    inference(resolution,[],[f132,f82])).

fof(f132,plain,(
    sP5(sK8,sK10,sK12) ),
    inference(resolution,[],[f131,f59])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK8)
      | sP5(sK8,X0,sK12) ) ),
    inference(subsumption_resolution,[],[f130,f64])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)
      | sP5(sK8,X0,sK12)
      | ~ m1_subset_1(X0,sK8) ) ),
    inference(resolution,[],[f97,f65])).

fof(f97,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
      | ~ v1_funct_2(sK12,k2_zfmisc_1(X3,X3),X3)
      | sP5(X3,X4,sK12)
      | ~ m1_subset_1(X4,X3) ) ),
    inference(resolution,[],[f63,f86])).

fof(f143,plain,
    ( spl13_6
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f133,f140,f136])).

fof(f133,plain,
    ( ~ r3_binop_1(sK8,sK10,sK12)
    | sP4(sK12,sK10,sK8) ),
    inference(resolution,[],[f132,f81])).

fof(f129,plain,
    ( ~ spl13_4
    | ~ spl13_5
    | spl13_1 ),
    inference(avatar_split_clause,[],[f120,f101,f126,f122])).

fof(f120,plain,
    ( ~ r2_binop_1(sK7,sK9,sK11)
    | ~ r1_binop_1(sK7,sK9,sK11)
    | spl13_1 ),
    inference(resolution,[],[f119,f85])).

fof(f119,plain,
    ( ~ sP4(sK11,sK9,sK7)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f113,f102])).

fof(f102,plain,
    ( ~ r3_binop_1(sK7,sK9,sK11)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f113,plain,
    ( ~ sP4(sK11,sK9,sK7)
    | r3_binop_1(sK7,sK9,sK11) ),
    inference(resolution,[],[f111,f82])).

fof(f111,plain,(
    sP5(sK7,sK9,sK11) ),
    inference(resolution,[],[f110,f58])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK7)
      | sP5(sK7,X0,sK11) ) ),
    inference(subsumption_resolution,[],[f109,f61])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)
      | sP5(sK7,X0,sK11)
      | ~ m1_subset_1(X0,sK7) ) ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
      | ~ v1_funct_2(sK11,k2_zfmisc_1(X3,X3),X3)
      | sP5(X3,X4,sK11)
      | ~ m1_subset_1(X4,X3) ) ),
    inference(resolution,[],[f60,f86])).

fof(f118,plain,
    ( spl13_3
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f112,f101,f115])).

fof(f112,plain,
    ( ~ r3_binop_1(sK7,sK9,sK11)
    | sP4(sK11,sK9,sK7) ),
    inference(resolution,[],[f111,f81])).

fof(f108,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f66,f105,f101])).

fof(f66,plain,
    ( r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))
    | r3_binop_1(sK7,sK9,sK11) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (31815)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (31822)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.51  % (31821)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.52  % (31820)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (31807)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.52  % (31823)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.52  % (31813)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.53  % (31816)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (31819)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.53  % (31818)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.53  % (31812)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.53  % (31811)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.53  % (31814)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.54  % (31825)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (31808)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.54  % (31810)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.54  % (31816)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.55  % (31826)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.55  % (31827)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.55  % (31809)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.55  % (31817)WARNING: option uwaf not known.
% 0.20/0.55  % (31824)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.56  % (31817)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f419,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f108,f118,f129,f143,f154,f310,f317,f322,f324,f339,f356,f361,f363,f375,f404,f407,f418])).
% 0.20/0.57  fof(f418,plain,(
% 0.20/0.57    ~spl13_3 | ~spl13_6 | spl13_15),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f417])).
% 0.20/0.57  fof(f417,plain,(
% 0.20/0.57    $false | (~spl13_3 | ~spl13_6 | spl13_15)),
% 0.20/0.57    inference(subsumption_resolution,[],[f416,f308])).
% 0.20/0.57  fof(f308,plain,(
% 0.20/0.57    ~sP2(sK12,sK10,sK8,sK11,sK9,sK7) | spl13_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f307])).
% 0.20/0.57  fof(f307,plain,(
% 0.20/0.57    spl13_15 <=> sP2(sK12,sK10,sK8,sK11,sK9,sK7)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 0.20/0.57  fof(f416,plain,(
% 0.20/0.57    sP2(sK12,sK10,sK8,sK11,sK9,sK7) | (~spl13_3 | ~spl13_6)),
% 0.20/0.57    inference(resolution,[],[f410,f408])).
% 0.20/0.57  fof(f408,plain,(
% 0.20/0.57    r1_binop_1(sK8,sK10,sK12) | ~spl13_6),
% 0.20/0.57    inference(resolution,[],[f138,f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r1_binop_1(X2,X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ~r2_binop_1(X2,X1,X0) | ~r1_binop_1(X2,X1,X0)) & ((r2_binop_1(X2,X1,X0) & r1_binop_1(X2,X1,X0)) | ~sP4(X0,X1,X2)))),
% 0.20/0.57    inference(rectify,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | ~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2)) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~sP4(X2,X1,X0)))),
% 0.20/0.57    inference(flattening,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | (~r2_binop_1(X0,X1,X2) | ~r1_binop_1(X0,X1,X2))) & ((r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)) | ~sP4(X2,X1,X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X2,X1,X0] : (sP4(X2,X1,X0) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    sP4(sK12,sK10,sK8) | ~spl13_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f136])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    spl13_6 <=> sP4(sK12,sK10,sK8)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_binop_1(X0,X1,X2) | sP2(X2,X1,X0,sK11,sK9,sK7)) ) | ~spl13_3),
% 0.20/0.57    inference(resolution,[],[f365,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_binop_1(X5,X4,X3) | ~r1_binop_1(X2,X1,X0) | sP2(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3,X4,X5] : ((sP2(X0,X1,X2,X3,X4,X5) | ~r1_binop_1(X2,X1,X0) | ~r1_binop_1(X5,X4,X3)) & ((r1_binop_1(X2,X1,X0) & r1_binop_1(X5,X4,X3)) | ~sP2(X0,X1,X2,X3,X4,X5)))),
% 0.20/0.57    inference(rectify,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ! [X5,X3,X1,X4,X2,X0] : ((sP2(X5,X3,X1,X4,X2,X0) | ~r1_binop_1(X1,X3,X5) | ~r1_binop_1(X0,X2,X4)) & ((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) | ~sP2(X5,X3,X1,X4,X2,X0)))),
% 0.20/0.57    inference(flattening,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X5,X3,X1,X4,X2,X0] : ((sP2(X5,X3,X1,X4,X2,X0) | (~r1_binop_1(X1,X3,X5) | ~r1_binop_1(X0,X2,X4))) & ((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) | ~sP2(X5,X3,X1,X4,X2,X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X5,X3,X1,X4,X2,X0] : (sP2(X5,X3,X1,X4,X2,X0) <=> (r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)))),
% 0.20/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.57  fof(f365,plain,(
% 0.20/0.57    r1_binop_1(sK7,sK9,sK11) | ~spl13_3),
% 0.20/0.57    inference(resolution,[],[f117,f83])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    sP4(sK11,sK9,sK7) | ~spl13_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f115])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    spl13_3 <=> sP4(sK11,sK9,sK7)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.20/0.57  fof(f407,plain,(
% 0.20/0.57    spl13_2 | spl13_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f406])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    $false | (spl13_2 | spl13_7)),
% 0.20/0.57    inference(subsumption_resolution,[],[f142,f405])).
% 0.20/0.57  fof(f405,plain,(
% 0.20/0.57    r3_binop_1(sK8,sK10,sK12) | spl13_2),
% 0.20/0.57    inference(subsumption_resolution,[],[f67,f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | spl13_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    spl13_2 <=> r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | r3_binop_1(sK8,sK10,sK12)),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ((((((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~r3_binop_1(sK8,sK10,sK12) | ~r3_binop_1(sK7,sK9,sK11)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | (r3_binop_1(sK8,sK10,sK12) & r3_binop_1(sK7,sK9,sK11))) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(sK12)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(sK11)) & m1_subset_1(sK10,sK8)) & m1_subset_1(sK9,sK7)) & ~v1_xboole_0(sK8)) & ~v1_xboole_0(sK7)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11,sK12])],[f32,f38,f37,f36,f35,f34,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(sK7,X2,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(sK7,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,sK7)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK7))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(sK7,X2,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,X1),k1_domain_1(sK7,X1,X2,X3),k6_filter_1(sK7,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(sK7,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,sK7)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,X3,X5) | ~r3_binop_1(sK7,X2,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,X3,X5) & r3_binop_1(sK7,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,sK8)) & m1_subset_1(X2,sK7)) & ~v1_xboole_0(sK8))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,X3,X5) | ~r3_binop_1(sK7,X2,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X2,X3),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,X3,X5) & r3_binop_1(sK7,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,sK8)) & m1_subset_1(X2,sK7)) => (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,X3,X5) | ~r3_binop_1(sK7,sK9,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,X3,X5) & r3_binop_1(sK7,sK9,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,sK8)) & m1_subset_1(sK9,sK7))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,X3,X5) | ~r3_binop_1(sK7,sK9,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,X3),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,X3,X5) & r3_binop_1(sK7,sK9,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(X3,sK8)) => (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,sK10,X5) | ~r3_binop_1(sK7,sK9,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,sK10,X5) & r3_binop_1(sK7,sK9,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) & m1_subset_1(sK10,sK8))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5)) | ~r3_binop_1(sK8,sK10,X5) | ~r3_binop_1(sK7,sK9,X4)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,X4,X5)) | (r3_binop_1(sK8,sK10,X5) & r3_binop_1(sK7,sK9,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(X4,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(X4)) => (? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5)) | ~r3_binop_1(sK8,sK10,X5) | ~r3_binop_1(sK7,sK9,sK11)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5)) | (r3_binop_1(sK8,sK10,X5) & r3_binop_1(sK7,sK9,sK11))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7))) & v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) & v1_funct_1(sK11))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ? [X5] : ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5)) | ~r3_binop_1(sK8,sK10,X5) | ~r3_binop_1(sK7,sK9,sK11)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,X5)) | (r3_binop_1(sK8,sK10,X5) & r3_binop_1(sK7,sK9,sK11))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(X5,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(X5)) => ((~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~r3_binop_1(sK8,sK10,sK12) | ~r3_binop_1(sK7,sK9,sK11)) & (r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | (r3_binop_1(sK8,sK10,sK12) & r3_binop_1(sK7,sK9,sK11))) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) & v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) & v1_funct_1(sK12))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4)) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.57    inference(flattening,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (~r3_binop_1(X1,X3,X5) | ~r3_binop_1(X0,X2,X4))) & (r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | (r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f8])).
% 0.20/0.58  fof(f8,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <~> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4))) & m1_subset_1(X3,X1)) & m1_subset_1(X2,X0)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,negated_conjecture,(
% 0.20/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 0.20/0.58    inference(negated_conjecture,[],[f6])).
% 0.20/0.58  fof(f6,conjecture,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r3_binop_1(X1,X3,X5) & r3_binop_1(X0,X2,X4)) <=> r3_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_filter_1)).
% 0.20/0.58  fof(f142,plain,(
% 0.20/0.58    ~r3_binop_1(sK8,sK10,sK12) | spl13_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f140])).
% 0.20/0.58  fof(f140,plain,(
% 0.20/0.58    spl13_7 <=> r3_binop_1(sK8,sK10,sK12)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 0.20/0.58  fof(f404,plain,(
% 0.20/0.58    spl13_2 | ~spl13_3 | ~spl13_6 | ~spl13_14 | ~spl13_15 | ~spl13_16),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f403])).
% 0.20/0.58  fof(f403,plain,(
% 0.20/0.58    $false | (spl13_2 | ~spl13_3 | ~spl13_6 | ~spl13_14 | ~spl13_15 | ~spl13_16)),
% 0.20/0.58    inference(subsumption_resolution,[],[f402,f368])).
% 0.20/0.58  fof(f368,plain,(
% 0.20/0.58    r2_binop_1(sK8,sK10,sK12) | ~spl13_6),
% 0.20/0.58    inference(resolution,[],[f138,f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r2_binop_1(X2,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f402,plain,(
% 0.20/0.58    ~r2_binop_1(sK8,sK10,sK12) | (spl13_2 | ~spl13_3 | ~spl13_14 | ~spl13_15 | ~spl13_16)),
% 0.20/0.58    inference(resolution,[],[f401,f370])).
% 0.20/0.58  fof(f370,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,sK11,sK9,sK7) | ~r2_binop_1(X0,X1,X2)) ) | ~spl13_3),
% 0.20/0.58    inference(resolution,[],[f366,f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_binop_1(X5,X4,X3) | ~r2_binop_1(X2,X1,X0) | sP0(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ~r2_binop_1(X2,X1,X0) | ~r2_binop_1(X5,X4,X3)) & ((r2_binop_1(X2,X1,X0) & r2_binop_1(X5,X4,X3)) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 0.20/0.58    inference(rectify,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ! [X5,X3,X1,X4,X2,X0] : ((sP0(X5,X3,X1,X4,X2,X0) | ~r2_binop_1(X1,X3,X5) | ~r2_binop_1(X0,X2,X4)) & ((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) | ~sP0(X5,X3,X1,X4,X2,X0)))),
% 0.20/0.58    inference(flattening,[],[f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ! [X5,X3,X1,X4,X2,X0] : ((sP0(X5,X3,X1,X4,X2,X0) | (~r2_binop_1(X1,X3,X5) | ~r2_binop_1(X0,X2,X4))) & ((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) | ~sP0(X5,X3,X1,X4,X2,X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X5,X3,X1,X4,X2,X0] : (sP0(X5,X3,X1,X4,X2,X0) <=> (r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.58  fof(f366,plain,(
% 0.20/0.58    r2_binop_1(sK7,sK9,sK11) | ~spl13_3),
% 0.20/0.58    inference(resolution,[],[f117,f84])).
% 0.20/0.58  fof(f401,plain,(
% 0.20/0.58    ~sP0(sK12,sK10,sK8,sK11,sK9,sK7) | (spl13_2 | ~spl13_14 | ~spl13_15 | ~spl13_16)),
% 0.20/0.58    inference(subsumption_resolution,[],[f357,f400])).
% 0.20/0.58  fof(f400,plain,(
% 0.20/0.58    ~r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | (spl13_2 | ~spl13_14 | ~spl13_15)),
% 0.20/0.58    inference(subsumption_resolution,[],[f396,f379])).
% 0.20/0.58  fof(f379,plain,(
% 0.20/0.58    r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | (~spl13_14 | ~spl13_15)),
% 0.20/0.58    inference(subsumption_resolution,[],[f318,f309])).
% 0.20/0.58  fof(f309,plain,(
% 0.20/0.58    sP2(sK12,sK10,sK8,sK11,sK9,sK7) | ~spl13_15),
% 0.20/0.58    inference(avatar_component_clause,[],[f307])).
% 0.20/0.58  fof(f318,plain,(
% 0.20/0.58    ~sP2(sK12,sK10,sK8,sK11,sK9,sK7) | r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~spl13_14),
% 0.20/0.58    inference(resolution,[],[f304,f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3,X4,X5) | ~sP2(X0,X4,X2,X1,X5,X3) | r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : (((sP2(X0,X4,X2,X1,X5,X3) | ~r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))) & (r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) | ~sP2(X0,X4,X2,X1,X5,X3))) | ~sP3(X0,X1,X2,X3,X4,X5))),
% 0.20/0.58    inference(rectify,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X5,X4,X1,X0,X3,X2] : (((sP2(X5,X3,X1,X4,X2,X0) | ~r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~sP2(X5,X3,X1,X4,X2,X0))) | ~sP3(X5,X4,X1,X0,X3,X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X5,X4,X1,X0,X3,X2] : ((sP2(X5,X3,X1,X4,X2,X0) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~sP3(X5,X4,X1,X0,X3,X2))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.58  fof(f304,plain,(
% 0.20/0.58    sP3(sK12,sK11,sK8,sK7,sK10,sK9) | ~spl13_14),
% 0.20/0.58    inference(avatar_component_clause,[],[f303])).
% 0.20/0.58  fof(f303,plain,(
% 0.20/0.58    spl13_14 <=> sP3(sK12,sK11,sK8,sK7,sK10,sK9)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 0.20/0.58  fof(f396,plain,(
% 0.20/0.58    ~r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | spl13_2),
% 0.20/0.58    inference(resolution,[],[f395,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | ~r2_binop_1(X2,X1,X0) | ~r1_binop_1(X2,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f395,plain,(
% 0.20/0.58    ~sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8)) | spl13_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f294,f106])).
% 0.20/0.58  fof(f294,plain,(
% 0.20/0.58    ~sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8)) | r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))),
% 0.20/0.58    inference(resolution,[],[f292,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | r3_binop_1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f50])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((r3_binop_1(X0,X1,X2) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r3_binop_1(X0,X1,X2))) | ~sP5(X0,X1,X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r3_binop_1(X0,X1,X2) <=> sP4(X2,X1,X0)) | ~sP5(X0,X1,X2))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.58  fof(f292,plain,(
% 0.20/0.58    sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12))),
% 0.20/0.58    inference(resolution,[],[f291,f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    m1_subset_1(sK9,sK7)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f291,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,sK7) | sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,sK10),k6_filter_1(sK7,sK8,sK11,sK12))) )),
% 0.20/0.58    inference(resolution,[],[f290,f59])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    m1_subset_1(sK10,sK8)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f290,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,sK8) | sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12)) | ~m1_subset_1(X0,sK7)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f289,f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ~v1_xboole_0(sK7)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f289,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12)) | ~m1_subset_1(X1,sK8) | ~m1_subset_1(X0,sK7) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f288,f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ~v1_xboole_0(sK8)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f288,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sP5(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,X0,X1),k6_filter_1(sK7,sK8,sK11,sK12)) | ~m1_subset_1(X1,sK8) | ~m1_subset_1(X0,sK7) | v1_xboole_0(sK8) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(resolution,[],[f287,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f16])).
% 0.20/0.58  fof(f16,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) | (~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X1) & m1_subset_1(X2,X0) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_domain_1)).
% 0.20/0.58  fof(f287,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,k2_zfmisc_1(sK7,sK8)) | sP5(k2_zfmisc_1(sK7,sK8),X0,k6_filter_1(sK7,sK8,sK11,sK12))) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f286,f172])).
% 0.20/0.58  fof(f172,plain,(
% 0.20/0.58    v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))),
% 0.20/0.58    inference(resolution,[],[f170,f89])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~sP6(X0,X1,X2,X3) | v1_funct_2(k6_filter_1(X1,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k6_filter_1(X1,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0)))) & v1_funct_2(k6_filter_1(X1,X0,X3,X2),k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0)) & v1_funct_1(k6_filter_1(X1,X0,X3,X2))) | ~sP6(X0,X1,X2,X3))),
% 0.20/0.58    inference(rectify,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X1,X0,X3,X2] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | ~sP6(X1,X0,X3,X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X1,X0,X3,X2] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | ~sP6(X1,X0,X3,X2))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.58  fof(f170,plain,(
% 0.20/0.58    sP6(sK8,sK7,sK12,sK11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f169,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f169,plain,(
% 0.20/0.58    ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | sP6(sK8,sK7,sK12,sK11)),
% 0.20/0.58    inference(resolution,[],[f158,f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f158,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(sK12,k2_zfmisc_1(X1,X1),X1) | sP6(X1,sK7,sK12,sK11)) )),
% 0.20/0.58    inference(resolution,[],[f156,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    v1_funct_1(sK12)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | sP6(X1,sK7,X0,sK11)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f155,f61])).
% 0.20/0.58  fof(f61,plain,(
% 0.20/0.58    v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) | sP6(X1,sK7,X0,sK11)) )),
% 0.20/0.58    inference(resolution,[],[f92,f62])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK7),sK7)))),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X2),X2))) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(sK11,k2_zfmisc_1(X2,X2),X2) | sP6(X1,X2,X0,sK11)) )),
% 0.20/0.58    inference(resolution,[],[f60,f91])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | sP6(X1,X0,X3,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (sP6(X1,X0,X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(definition_folding,[],[f19,f29])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)))) & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1)) & v1_funct_1(k6_filter_1(X0,X1,X2,X3))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    v1_funct_1(sK11)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f286,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8)) | sP5(k2_zfmisc_1(sK7,sK8),X0,k6_filter_1(sK7,sK8,sK11,sK12)) | ~m1_subset_1(X0,k2_zfmisc_1(sK7,sK8))) )),
% 0.20/0.58    inference(resolution,[],[f176,f173])).
% 0.20/0.58  fof(f173,plain,(
% 0.20/0.58    m1_subset_1(k6_filter_1(sK7,sK8,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK7,sK8),k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))))),
% 0.20/0.58    inference(resolution,[],[f170,f90])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~sP6(X0,X1,X2,X3) | m1_subset_1(k6_filter_1(X1,X0,X3,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X1,X0)),k2_zfmisc_1(X1,X0))))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f176,plain,(
% 0.20/0.58    ( ! [X4,X5] : (~m1_subset_1(k6_filter_1(sK7,sK8,sK11,sK12),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X4,X4),X4))) | ~v1_funct_2(k6_filter_1(sK7,sK8,sK11,sK12),k2_zfmisc_1(X4,X4),X4) | sP5(X4,X5,k6_filter_1(sK7,sK8,sK11,sK12)) | ~m1_subset_1(X5,X4)) )),
% 0.20/0.58    inference(resolution,[],[f171,f86])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | sP5(X0,X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (sP5(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.20/0.58    inference(definition_folding,[],[f15,f27,f26])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2)) | ~m1_subset_1(X1,X0))),
% 0.20/0.58    inference(flattening,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : ((r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X1,X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X2)) => (r3_binop_1(X0,X1,X2) <=> (r2_binop_1(X0,X1,X2) & r1_binop_1(X0,X1,X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).
% 0.20/0.58  fof(f171,plain,(
% 0.20/0.58    v1_funct_1(k6_filter_1(sK7,sK8,sK11,sK12))),
% 0.20/0.58    inference(resolution,[],[f170,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~sP6(X0,X1,X2,X3) | v1_funct_1(k6_filter_1(X1,X0,X3,X2))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f357,plain,(
% 0.20/0.58    ~sP0(sK12,sK10,sK8,sK11,sK9,sK7) | r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~spl13_16),
% 0.20/0.58    inference(resolution,[],[f333,f69])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5) | ~sP0(X0,X4,X2,X1,X5,X3) | r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : (((sP0(X0,X4,X2,X1,X5,X3) | ~r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0))) & (r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) | ~sP0(X0,X4,X2,X1,X5,X3))) | ~sP1(X0,X1,X2,X3,X4,X5))),
% 0.20/0.58    inference(rectify,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X5,X4,X1,X0,X3,X2] : (((sP0(X5,X3,X1,X4,X2,X0) | ~r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) & (r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)) | ~sP0(X5,X3,X1,X4,X2,X0))) | ~sP1(X5,X4,X1,X0,X3,X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X5,X4,X1,X0,X3,X2] : ((sP0(X5,X3,X1,X4,X2,X0) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~sP1(X5,X4,X1,X0,X3,X2))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.58  fof(f333,plain,(
% 0.20/0.58    sP1(sK12,sK11,sK8,sK7,sK10,sK9) | ~spl13_16),
% 0.20/0.58    inference(avatar_component_clause,[],[f332])).
% 0.20/0.58  fof(f332,plain,(
% 0.20/0.58    spl13_16 <=> sP1(sK12,sK11,sK8,sK7,sK10,sK9)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 0.20/0.58  fof(f375,plain,(
% 0.20/0.58    ~spl13_1 | ~spl13_2 | ~spl13_7),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f374])).
% 0.20/0.58  fof(f374,plain,(
% 0.20/0.58    $false | (~spl13_1 | ~spl13_2 | ~spl13_7)),
% 0.20/0.58    inference(subsumption_resolution,[],[f373,f103])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    r3_binop_1(sK7,sK9,sK11) | ~spl13_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f101])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    spl13_1 <=> r3_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.20/0.58  fof(f373,plain,(
% 0.20/0.58    ~r3_binop_1(sK7,sK9,sK11) | (~spl13_2 | ~spl13_7)),
% 0.20/0.58    inference(subsumption_resolution,[],[f364,f141])).
% 0.20/0.58  fof(f141,plain,(
% 0.20/0.58    r3_binop_1(sK8,sK10,sK12) | ~spl13_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f140])).
% 0.20/0.58  fof(f364,plain,(
% 0.20/0.58    ~r3_binop_1(sK8,sK10,sK12) | ~r3_binop_1(sK7,sK9,sK11) | ~spl13_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f68,f107])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~spl13_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f105])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~r3_binop_1(sK8,sK10,sK12) | ~r3_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  fof(f363,plain,(
% 0.20/0.58    spl13_9 | ~spl13_17),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f362])).
% 0.20/0.58  fof(f362,plain,(
% 0.20/0.58    $false | (spl13_9 | ~spl13_17)),
% 0.20/0.58    inference(subsumption_resolution,[],[f359,f153])).
% 0.20/0.58  fof(f153,plain,(
% 0.20/0.58    ~r2_binop_1(sK8,sK10,sK12) | spl13_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f151])).
% 0.20/0.58  fof(f151,plain,(
% 0.20/0.58    spl13_9 <=> r2_binop_1(sK8,sK10,sK12)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.20/0.58  fof(f359,plain,(
% 0.20/0.58    r2_binop_1(sK8,sK10,sK12) | ~spl13_17),
% 0.20/0.58    inference(resolution,[],[f338,f72])).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | r2_binop_1(X2,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f44])).
% 0.20/0.58  fof(f338,plain,(
% 0.20/0.58    sP0(sK12,sK10,sK8,sK11,sK9,sK7) | ~spl13_17),
% 0.20/0.58    inference(avatar_component_clause,[],[f336])).
% 0.20/0.58  fof(f336,plain,(
% 0.20/0.58    spl13_17 <=> sP0(sK12,sK10,sK8,sK11,sK9,sK7)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 0.20/0.58  fof(f361,plain,(
% 0.20/0.58    spl13_5 | ~spl13_17),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f360])).
% 0.20/0.58  fof(f360,plain,(
% 0.20/0.58    $false | (spl13_5 | ~spl13_17)),
% 0.20/0.58    inference(subsumption_resolution,[],[f358,f128])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    ~r2_binop_1(sK7,sK9,sK11) | spl13_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f126])).
% 0.20/0.58  fof(f126,plain,(
% 0.20/0.58    spl13_5 <=> r2_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.20/0.58  fof(f358,plain,(
% 0.20/0.58    r2_binop_1(sK7,sK9,sK11) | ~spl13_17),
% 0.20/0.58    inference(resolution,[],[f338,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | r2_binop_1(X5,X4,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f44])).
% 0.20/0.58  fof(f356,plain,(
% 0.20/0.58    spl13_16),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f355])).
% 0.20/0.58  fof(f355,plain,(
% 0.20/0.58    $false | spl13_16),
% 0.20/0.58    inference(subsumption_resolution,[],[f354,f57])).
% 0.20/0.58  fof(f354,plain,(
% 0.20/0.58    v1_xboole_0(sK8) | spl13_16),
% 0.20/0.58    inference(subsumption_resolution,[],[f353,f64])).
% 0.20/0.58  fof(f353,plain,(
% 0.20/0.58    ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_16),
% 0.20/0.58    inference(subsumption_resolution,[],[f352,f59])).
% 0.20/0.58  fof(f352,plain,(
% 0.20/0.58    ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_16),
% 0.20/0.58    inference(subsumption_resolution,[],[f351,f63])).
% 0.20/0.58  fof(f351,plain,(
% 0.20/0.58    ~v1_funct_1(sK12) | ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_16),
% 0.20/0.58    inference(subsumption_resolution,[],[f350,f65])).
% 0.20/0.58  fof(f350,plain,(
% 0.20/0.58    ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) | ~v1_funct_1(sK12) | ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_16),
% 0.20/0.58    inference(resolution,[],[f348,f334])).
% 0.20/0.58  fof(f334,plain,(
% 0.20/0.58    ~sP1(sK12,sK11,sK8,sK7,sK10,sK9) | spl13_16),
% 0.20/0.58    inference(avatar_component_clause,[],[f332])).
% 0.20/0.58  fof(f348,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP1(X0,sK11,X1,sK7,X2,sK9) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X2,X1) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(resolution,[],[f342,f58])).
% 0.20/0.58  fof(f342,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,sK7) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | sP1(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f341,f56])).
% 0.20/0.58  fof(f341,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | sP1(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,sK7) | v1_xboole_0(X1) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f340,f61])).
% 0.20/0.58  fof(f340,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) | sP1(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,sK7) | v1_xboole_0(X1) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(resolution,[],[f95,f62])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ( ! [X14,X12,X10,X13,X11] : (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X12,X12),X12))) | ~v1_funct_2(X10,k2_zfmisc_1(X11,X11),X11) | ~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X11,X11),X11))) | ~v1_funct_2(sK11,k2_zfmisc_1(X12,X12),X12) | sP1(X10,sK11,X11,X12,X13,X14) | ~m1_subset_1(X13,X11) | ~m1_subset_1(X14,X12) | v1_xboole_0(X11) | v1_xboole_0(X12)) )),
% 0.20/0.58    inference(resolution,[],[f60,f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | sP1(X5,X4,X1,X0,X3,X2) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (sP1(X5,X4,X1,X0,X3,X2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(definition_folding,[],[f11,f21,f20])).
% 0.20/0.58  fof(f11,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f10])).
% 0.20/0.58  fof(f10,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4))) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r2_binop_1(X1,X3,X5) & r2_binop_1(X0,X2,X4)) <=> r2_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_filter_1)).
% 0.20/0.58  fof(f339,plain,(
% 0.20/0.58    ~spl13_16 | spl13_17 | ~spl13_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f300,f105,f336,f332])).
% 0.20/0.58  fof(f300,plain,(
% 0.20/0.58    sP0(sK12,sK10,sK8,sK11,sK9,sK7) | ~sP1(sK12,sK11,sK8,sK7,sK10,sK9) | ~spl13_2),
% 0.20/0.58    inference(resolution,[],[f297,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) | sP0(X0,X4,X2,X1,X5,X3) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f297,plain,(
% 0.20/0.58    r2_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~spl13_2),
% 0.20/0.58    inference(resolution,[],[f295,f84])).
% 0.20/0.58  fof(f295,plain,(
% 0.20/0.58    sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8)) | ~spl13_2),
% 0.20/0.58    inference(subsumption_resolution,[],[f293,f107])).
% 0.20/0.58  fof(f293,plain,(
% 0.20/0.58    ~r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | sP4(k6_filter_1(sK7,sK8,sK11,sK12),k1_domain_1(sK7,sK8,sK9,sK10),k2_zfmisc_1(sK7,sK8))),
% 0.20/0.58    inference(resolution,[],[f292,f81])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~r3_binop_1(X0,X1,X2) | sP4(X2,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f50])).
% 0.20/0.58  fof(f324,plain,(
% 0.20/0.58    spl13_8 | ~spl13_15),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.58  fof(f323,plain,(
% 0.20/0.58    $false | (spl13_8 | ~spl13_15)),
% 0.20/0.58    inference(subsumption_resolution,[],[f320,f149])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    ~r1_binop_1(sK8,sK10,sK12) | spl13_8),
% 0.20/0.58    inference(avatar_component_clause,[],[f147])).
% 0.20/0.58  fof(f147,plain,(
% 0.20/0.58    spl13_8 <=> r1_binop_1(sK8,sK10,sK12)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 0.20/0.58  fof(f320,plain,(
% 0.20/0.58    r1_binop_1(sK8,sK10,sK12) | ~spl13_15),
% 0.20/0.58    inference(resolution,[],[f309,f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5) | r1_binop_1(X2,X1,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f49])).
% 0.20/0.58  fof(f322,plain,(
% 0.20/0.58    spl13_4 | ~spl13_15),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.58  fof(f321,plain,(
% 0.20/0.58    $false | (spl13_4 | ~spl13_15)),
% 0.20/0.58    inference(subsumption_resolution,[],[f319,f124])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    ~r1_binop_1(sK7,sK9,sK11) | spl13_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f122])).
% 0.20/0.58  fof(f122,plain,(
% 0.20/0.58    spl13_4 <=> r1_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.20/0.58  fof(f319,plain,(
% 0.20/0.58    r1_binop_1(sK7,sK9,sK11) | ~spl13_15),
% 0.20/0.58    inference(resolution,[],[f309,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5) | r1_binop_1(X5,X4,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f49])).
% 0.20/0.58  fof(f317,plain,(
% 0.20/0.58    spl13_14),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f316])).
% 0.20/0.58  fof(f316,plain,(
% 0.20/0.58    $false | spl13_14),
% 0.20/0.58    inference(subsumption_resolution,[],[f315,f57])).
% 0.20/0.58  fof(f315,plain,(
% 0.20/0.58    v1_xboole_0(sK8) | spl13_14),
% 0.20/0.58    inference(subsumption_resolution,[],[f314,f64])).
% 0.20/0.58  fof(f314,plain,(
% 0.20/0.58    ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_14),
% 0.20/0.58    inference(subsumption_resolution,[],[f313,f59])).
% 0.20/0.58  fof(f313,plain,(
% 0.20/0.58    ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_14),
% 0.20/0.58    inference(subsumption_resolution,[],[f312,f63])).
% 0.20/0.58  fof(f312,plain,(
% 0.20/0.58    ~v1_funct_1(sK12) | ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_14),
% 0.20/0.58    inference(subsumption_resolution,[],[f311,f65])).
% 0.20/0.58  fof(f311,plain,(
% 0.20/0.58    ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) | ~v1_funct_1(sK12) | ~m1_subset_1(sK10,sK8) | ~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | v1_xboole_0(sK8) | spl13_14),
% 0.20/0.58    inference(resolution,[],[f305,f284])).
% 0.20/0.58  fof(f284,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP3(X0,sK11,X1,sK7,X2,sK9) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_1(X0) | ~m1_subset_1(X2,X1) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(resolution,[],[f273,f58])).
% 0.20/0.58  fof(f273,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,sK7) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | sP3(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | v1_xboole_0(X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f272,f56])).
% 0.20/0.58  fof(f272,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | sP3(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,sK7) | v1_xboole_0(X1) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f271,f61])).
% 0.20/0.58  fof(f271,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) | sP3(X0,sK11,X1,sK7,X2,X3) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X3,sK7) | v1_xboole_0(X1) | v1_xboole_0(sK7)) )),
% 0.20/0.58    inference(resolution,[],[f94,f62])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X6,X8,X7,X5,X9] : (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X7,X7),X7))) | ~v1_funct_2(X5,k2_zfmisc_1(X6,X6),X6) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X6,X6),X6))) | ~v1_funct_2(sK11,k2_zfmisc_1(X7,X7),X7) | sP3(X5,sK11,X6,X7,X8,X9) | ~m1_subset_1(X8,X6) | ~m1_subset_1(X9,X7) | v1_xboole_0(X6) | v1_xboole_0(X7)) )),
% 0.20/0.58    inference(resolution,[],[f60,f80])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | sP3(X5,X4,X1,X0,X3,X2) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (sP3(X5,X4,X1,X0,X3,X2) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(definition_folding,[],[f13,f24,f23])).
% 0.20/0.58  fof(f13,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) | ~v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) | ~v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) | ~v1_funct_1(X4))) | ~m1_subset_1(X3,X1)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X1) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0))) & v1_funct_2(X4,k2_zfmisc_1(X0,X0),X0) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1))) & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1) & v1_funct_1(X5)) => ((r1_binop_1(X1,X3,X5) & r1_binop_1(X0,X2,X4)) <=> r1_binop_1(k2_zfmisc_1(X0,X1),k1_domain_1(X0,X1,X2,X3),k6_filter_1(X0,X1,X4,X5)))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_filter_1)).
% 0.20/0.58  fof(f305,plain,(
% 0.20/0.58    ~sP3(sK12,sK11,sK8,sK7,sK10,sK9) | spl13_14),
% 0.20/0.58    inference(avatar_component_clause,[],[f303])).
% 0.20/0.58  fof(f310,plain,(
% 0.20/0.58    ~spl13_14 | spl13_15 | ~spl13_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f298,f105,f307,f303])).
% 0.20/0.58  fof(f298,plain,(
% 0.20/0.58    sP2(sK12,sK10,sK8,sK11,sK9,sK7) | ~sP3(sK12,sK11,sK8,sK7,sK10,sK9) | ~spl13_2),
% 0.20/0.58    inference(resolution,[],[f296,f76])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_binop_1(k2_zfmisc_1(X3,X2),k1_domain_1(X3,X2,X5,X4),k6_filter_1(X3,X2,X1,X0)) | sP2(X0,X4,X2,X1,X5,X3) | ~sP3(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f296,plain,(
% 0.20/0.58    r1_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | ~spl13_2),
% 0.20/0.58    inference(resolution,[],[f295,f83])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    ~spl13_8 | ~spl13_9 | spl13_7),
% 0.20/0.58    inference(avatar_split_clause,[],[f145,f140,f151,f147])).
% 0.20/0.58  fof(f145,plain,(
% 0.20/0.58    ~r2_binop_1(sK8,sK10,sK12) | ~r1_binop_1(sK8,sK10,sK12) | spl13_7),
% 0.20/0.58    inference(resolution,[],[f144,f85])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    ~sP4(sK12,sK10,sK8) | spl13_7),
% 0.20/0.58    inference(subsumption_resolution,[],[f134,f142])).
% 0.20/0.58  fof(f134,plain,(
% 0.20/0.58    ~sP4(sK12,sK10,sK8) | r3_binop_1(sK8,sK10,sK12)),
% 0.20/0.58    inference(resolution,[],[f132,f82])).
% 0.20/0.58  fof(f132,plain,(
% 0.20/0.58    sP5(sK8,sK10,sK12)),
% 0.20/0.58    inference(resolution,[],[f131,f59])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,sK8) | sP5(sK8,X0,sK12)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f130,f64])).
% 0.20/0.58  fof(f130,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_funct_2(sK12,k2_zfmisc_1(sK8,sK8),sK8) | sP5(sK8,X0,sK12) | ~m1_subset_1(X0,sK8)) )),
% 0.20/0.58    inference(resolution,[],[f97,f65])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X4,X3] : (~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3))) | ~v1_funct_2(sK12,k2_zfmisc_1(X3,X3),X3) | sP5(X3,X4,sK12) | ~m1_subset_1(X4,X3)) )),
% 0.20/0.58    inference(resolution,[],[f63,f86])).
% 0.20/0.58  fof(f143,plain,(
% 0.20/0.58    spl13_6 | ~spl13_7),
% 0.20/0.58    inference(avatar_split_clause,[],[f133,f140,f136])).
% 0.20/0.58  fof(f133,plain,(
% 0.20/0.58    ~r3_binop_1(sK8,sK10,sK12) | sP4(sK12,sK10,sK8)),
% 0.20/0.58    inference(resolution,[],[f132,f81])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    ~spl13_4 | ~spl13_5 | spl13_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f120,f101,f126,f122])).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    ~r2_binop_1(sK7,sK9,sK11) | ~r1_binop_1(sK7,sK9,sK11) | spl13_1),
% 0.20/0.58    inference(resolution,[],[f119,f85])).
% 0.20/0.58  fof(f119,plain,(
% 0.20/0.58    ~sP4(sK11,sK9,sK7) | spl13_1),
% 0.20/0.58    inference(subsumption_resolution,[],[f113,f102])).
% 0.20/0.58  fof(f102,plain,(
% 0.20/0.58    ~r3_binop_1(sK7,sK9,sK11) | spl13_1),
% 0.20/0.58    inference(avatar_component_clause,[],[f101])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    ~sP4(sK11,sK9,sK7) | r3_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    inference(resolution,[],[f111,f82])).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    sP5(sK7,sK9,sK11)),
% 0.20/0.58    inference(resolution,[],[f110,f58])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,sK7) | sP5(sK7,X0,sK11)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f109,f61])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    ( ! [X0] : (~v1_funct_2(sK11,k2_zfmisc_1(sK7,sK7),sK7) | sP5(sK7,X0,sK11) | ~m1_subset_1(X0,sK7)) )),
% 0.20/0.58    inference(resolution,[],[f93,f62])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X4,X3] : (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3))) | ~v1_funct_2(sK11,k2_zfmisc_1(X3,X3),X3) | sP5(X3,X4,sK11) | ~m1_subset_1(X4,X3)) )),
% 0.20/0.58    inference(resolution,[],[f60,f86])).
% 0.20/0.58  fof(f118,plain,(
% 0.20/0.58    spl13_3 | ~spl13_1),
% 0.20/0.58    inference(avatar_split_clause,[],[f112,f101,f115])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ~r3_binop_1(sK7,sK9,sK11) | sP4(sK11,sK9,sK7)),
% 0.20/0.58    inference(resolution,[],[f111,f81])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    spl13_1 | spl13_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f66,f105,f101])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    r3_binop_1(k2_zfmisc_1(sK7,sK8),k1_domain_1(sK7,sK8,sK9,sK10),k6_filter_1(sK7,sK8,sK11,sK12)) | r3_binop_1(sK7,sK9,sK11)),
% 0.20/0.58    inference(cnf_transformation,[],[f39])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (31816)------------------------------
% 0.20/0.58  % (31816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (31816)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (31816)Memory used [KB]: 10362
% 0.20/0.58  % (31816)Time elapsed: 0.112 s
% 0.20/0.58  % (31816)------------------------------
% 0.20/0.58  % (31816)------------------------------
% 0.20/0.58  % (31806)Success in time 0.222 s
%------------------------------------------------------------------------------
