%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:16 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  297 ( 802 expanded)
%              Number of leaves         :   50 ( 264 expanded)
%              Depth                    :   20
%              Number of atoms          : 1108 (4791 expanded)
%              Number of equality atoms :  101 ( 563 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4551,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f155,f160,f165,f169,f792,f1459,f1549,f1963,f2113,f2128,f2133,f2455,f4215,f4306,f4524,f4536,f4544])).

fof(f4544,plain,
    ( spl13_13
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f3131,f473,f316])).

fof(f316,plain,
    ( spl13_13
  <=> ! [X5] : sP0(sK8,X5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f473,plain,
    ( spl13_15
  <=> ! [X5] : sP3(sK8,X5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f3131,plain,
    ( ! [X15] : sP0(sK8,X15,sK7)
    | ~ spl13_15 ),
    inference(resolution,[],[f3049,f474])).

fof(f474,plain,
    ( ! [X5] : sP3(sK8,X5,sK7)
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f473])).

fof(f3049,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f3041])).

fof(f3041,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | sP0(X0,X1,X2)
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f2079,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK10(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( r1_xboole_0(X0,sK10(X0,X1,X2))
          & r2_hidden(X1,sK10(X0,X1,X2))
          & v3_pre_topc(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X0,X4)
            | ~ r2_hidden(X1,X4)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X0,X3)
          & r2_hidden(X1,X3)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r1_xboole_0(X0,sK10(X0,X1,X2))
        & r2_hidden(X1,sK10(X0,X1,X2))
        & v3_pre_topc(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( r1_xboole_0(X0,X3)
            & r2_hidden(X1,X3)
            & v3_pre_topc(X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X0,X4)
            | ~ r2_hidden(X1,X4)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( r1_xboole_0(X1,X3)
            & r2_hidden(X2,X3)
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ~ r1_xboole_0(X1,X3)
            | ~ r2_hidden(X2,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3] :
          ( ~ r1_xboole_0(X1,X3)
          | ~ r2_hidden(X2,X3)
          | ~ v3_pre_topc(X3,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2079,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,sK10(X1,X2,X3))
      | ~ sP3(X0,X2,X3)
      | sP0(X1,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f2077])).

fof(f2077,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,sK10(X1,X2,X3))
      | ~ sP3(X0,X2,X3)
      | sP0(X1,X2,X3)
      | sP0(X1,X2,X3) ) ),
    inference(resolution,[],[f874,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK10(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f874,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,sK10(X9,X10,X11))
      | ~ r1_xboole_0(X12,sK10(X9,X10,X11))
      | ~ sP3(X12,X8,X11)
      | sP0(X9,X10,X11) ) ),
    inference(subsumption_resolution,[],[f871,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK10(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f871,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( ~ r2_hidden(X8,sK10(X9,X10,X11))
      | ~ v3_pre_topc(sK10(X9,X10,X11),X11)
      | ~ r1_xboole_0(X12,sK10(X9,X10,X11))
      | ~ sP3(X12,X8,X11)
      | sP0(X9,X10,X11) ) ),
    inference(resolution,[],[f122,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X1,X4)
      | ~ v3_pre_topc(X4,X2)
      | ~ r1_xboole_0(X0,X4)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( r1_xboole_0(X0,sK12(X0,X1,X2))
          & r2_hidden(X1,sK12(X0,X1,X2))
          & v3_pre_topc(sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X0,X4)
            | ~ r2_hidden(X1,X4)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X0,X3)
          & r2_hidden(X1,X3)
          & v3_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r1_xboole_0(X0,sK12(X0,X1,X2))
        & r2_hidden(X1,sK12(X0,X1,X2))
        & v3_pre_topc(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( r1_xboole_0(X0,X3)
            & r2_hidden(X1,X3)
            & v3_pre_topc(X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X0,X4)
            | ~ r2_hidden(X1,X4)
            | ~ v3_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | ? [X4] :
            ( r1_xboole_0(X1,X4)
            & r2_hidden(X3,X4)
            & v3_pre_topc(X4,X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X4] :
            ( ~ r1_xboole_0(X1,X4)
            | ~ r2_hidden(X3,X4)
            | ~ v3_pre_topc(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ! [X4] :
          ( ~ r1_xboole_0(X1,X4)
          | ~ r2_hidden(X3,X4)
          | ~ v3_pre_topc(X4,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f4536,plain,
    ( ~ spl13_76
    | spl13_4
    | ~ spl13_5
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f2398,f717,f162,f157,f2400])).

fof(f2400,plain,
    ( spl13_76
  <=> sP5(sK9,k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f157,plain,
    ( spl13_4
  <=> k1_xboole_0 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f162,plain,
    ( spl13_5
  <=> m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f717,plain,
    ( spl13_21
  <=> v4_pre_topc(k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f2398,plain,
    ( ~ sP5(sK9,k1_xboole_0,sK7)
    | spl13_4
    | ~ spl13_5
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f2397,f159])).

fof(f159,plain,
    ( k1_xboole_0 != sK9
    | spl13_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f2397,plain,
    ( ~ sP5(sK9,k1_xboole_0,sK7)
    | k1_xboole_0 = sK9
    | ~ spl13_5
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f2396,f82])).

fof(f82,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ( r1_xboole_0(sK8,sK9)
        & v3_pre_topc(sK9,sK7)
        & k1_xboole_0 != sK9
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) )
      | ~ v1_tops_1(sK8,sK7) )
    & ( ! [X3] :
          ( ~ r1_xboole_0(sK8,X3)
          | ~ v3_pre_topc(X3,sK7)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
      | v1_tops_1(sK8,sK7) )
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f53,f56,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v1_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,sK7)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
            | ~ v1_tops_1(X1,sK7) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,sK7)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
            | v1_tops_1(X1,sK7) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( r1_xboole_0(X1,X2)
              & v3_pre_topc(X2,sK7)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
          | ~ v1_tops_1(X1,sK7) )
        & ( ! [X3] :
              ( ~ r1_xboole_0(X1,X3)
              | ~ v3_pre_topc(X3,sK7)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
          | v1_tops_1(X1,sK7) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) )
   => ( ( ? [X2] :
            ( r1_xboole_0(sK8,X2)
            & v3_pre_topc(X2,sK7)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
        | ~ v1_tops_1(sK8,sK7) )
      & ( ! [X3] :
            ( ~ r1_xboole_0(sK8,X3)
            | ~ v3_pre_topc(X3,sK7)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
        | v1_tops_1(sK8,sK7) )
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X2] :
        ( r1_xboole_0(sK8,X2)
        & v3_pre_topc(X2,sK7)
        & k1_xboole_0 != X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7))) )
   => ( r1_xboole_0(sK8,sK9)
      & v3_pre_topc(sK9,sK7)
      & k1_xboole_0 != sK9
      & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X3] :
                ( ~ r1_xboole_0(X1,X3)
                | ~ v3_pre_topc(X3,X0)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r1_xboole_0(X1,X2)
                & v3_pre_topc(X2,X0)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v1_tops_1(X1,X0) )
          & ( ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v1_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_1(X1,X0)
          <~> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( r1_xboole_0(X1,X2)
                      & v3_pre_topc(X2,X0)
                      & k1_xboole_0 != X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

fof(f2396,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ sP5(sK9,k1_xboole_0,sK7)
    | k1_xboole_0 = sK9
    | ~ spl13_5
    | ~ spl13_21 ),
    inference(subsumption_resolution,[],[f2392,f718])).

fof(f718,plain,
    ( v4_pre_topc(k1_xboole_0,sK7)
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f717])).

fof(f2392,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK7)
    | ~ l1_pre_topc(sK7)
    | ~ sP5(sK9,k1_xboole_0,sK7)
    | k1_xboole_0 = sK9
    | ~ spl13_5 ),
    inference(resolution,[],[f1599,f610])).

fof(f610,plain,(
    ! [X2,X1] :
      ( ~ sP6(X1,k1_xboole_0,X2)
      | ~ v4_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | ~ sP5(X2,k1_xboole_0,X1)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f596,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X1) = X2
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_pre_topc(X0,X1) = X2
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | k2_pre_topc(X0,X1) != X2 ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_pre_topc(X0,X1) = X2
      <=> sP5(X2,X1,X0) )
      | ~ sP6(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f596,plain,(
    ! [X1] :
      ( k1_xboole_0 = k2_pre_topc(X1,k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1599,plain,
    ( sP6(sK7,k1_xboole_0,sK9)
    | ~ spl13_5 ),
    inference(resolution,[],[f1578,f90])).

fof(f1578,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK7)))
        | sP6(sK7,X5,sK9) )
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f1557,f82])).

fof(f1557,plain,
    ( ! [X5] :
        ( sP6(sK7,X5,sK9)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK7)))
        | ~ l1_pre_topc(sK7) )
    | ~ spl13_5 ),
    inference(resolution,[],[f164,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP6(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP6(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f34,f49,f48,f47,f46])).

fof(f47,plain,(
    ! [X0,X3,X1,X2] :
      ( sP4(X0,X3,X1,X2)
    <=> ( r2_hidden(X3,X2)
      <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( sP5(X2,X1,X0)
    <=> ! [X3] :
          ( sP4(X0,X3,X1,X2)
          | ~ r2_hidden(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( ~ r1_xboole_0(X1,X4)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X0)
                          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) )
                    | ~ r2_hidden(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k2_pre_topc(X0,X1) = X2
              <=> ! [X3] :
                    ( r2_hidden(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_xboole_0(X1,X4)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X0) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).

fof(f164,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f4524,plain,
    ( spl13_76
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_27 ),
    inference(avatar_split_clause,[],[f4513,f845,f642,f316,f162,f152,f147,f2400])).

fof(f147,plain,
    ( spl13_2
  <=> r1_xboole_0(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f152,plain,
    ( spl13_3
  <=> v3_pre_topc(sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f642,plain,
    ( spl13_19
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f845,plain,
    ( spl13_27
  <=> sP5(k1_xboole_0,k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f4513,plain,
    ( sP5(sK9,k1_xboole_0,sK7)
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_13
    | ~ spl13_19
    | ~ spl13_27 ),
    inference(resolution,[],[f4401,f1611])).

fof(f1611,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK9)
    | ~ spl13_2
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f1608,f149])).

fof(f149,plain,
    ( r1_xboole_0(sK8,sK9)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1608,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK8,sK9)
        | ~ r2_hidden(X0,sK9) )
    | ~ spl13_3
    | ~ spl13_5
    | ~ spl13_13 ),
    inference(resolution,[],[f1575,f317])).

fof(f317,plain,
    ( ! [X5] : sP0(sK8,X5,sK7)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f316])).

fof(f1575,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,X0,sK7)
        | ~ r1_xboole_0(X1,sK9)
        | ~ r2_hidden(X0,sK9) )
    | ~ spl13_3
    | ~ spl13_5 ),
    inference(subsumption_resolution,[],[f1554,f154])).

fof(f154,plain,
    ( v3_pre_topc(sK9,sK7)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1554,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK9)
        | ~ v3_pre_topc(sK9,sK7)
        | ~ r1_xboole_0(X1,sK9)
        | ~ sP0(X1,X0,sK7) )
    | ~ spl13_5 ),
    inference(resolution,[],[f164,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r2_hidden(X1,X4)
      | ~ v3_pre_topc(X4,X2)
      | ~ r1_xboole_0(X0,X4)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4401,plain,
    ( ! [X6] :
        ( r2_hidden(sK11(X6,k1_xboole_0,sK7),X6)
        | sP5(X6,k1_xboole_0,sK7) )
    | ~ spl13_19
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f4400,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ sP4(X2,sK11(X0,X1,X2),X1,X0)
          & r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( sP4(X2,X4,X1,X0)
            | ~ r2_hidden(X4,u1_struct_0(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP4(X2,X3,X1,X0)
          & r2_hidden(X3,u1_struct_0(X2)) )
     => ( ~ sP4(X2,sK11(X0,X1,X2),X1,X0)
        & r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ sP4(X2,X3,X1,X0)
            & r2_hidden(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( sP4(X2,X4,X1,X0)
            | ~ r2_hidden(X4,u1_struct_0(X2)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ( sP5(X2,X1,X0)
        | ? [X3] :
            ( ~ sP4(X0,X3,X1,X2)
            & r2_hidden(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( sP4(X0,X3,X1,X2)
            | ~ r2_hidden(X3,u1_struct_0(X0)) )
        | ~ sP5(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f4400,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK11(X6,k1_xboole_0,sK7),u1_struct_0(sK7))
        | r2_hidden(sK11(X6,k1_xboole_0,sK7),X6)
        | sP5(X6,k1_xboole_0,sK7) )
    | ~ spl13_19
    | ~ spl13_27 ),
    inference(resolution,[],[f4316,f422])).

fof(f422,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,sK11(X1,X0,X2),X2)
      | r2_hidden(sK11(X1,X0,X2),X1)
      | sP5(X1,X0,X2) ) ),
    inference(resolution,[],[f120,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,sK11(X0,X1,X2),X1,X0)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | sP3(X2,X1,X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(X2,X1,X0)
            | ~ r2_hidden(X1,X3) )
          & ( sP3(X2,X1,X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ sP3(X2,X1,X0) )
          & ( sP3(X2,X1,X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1,X2] :
      ( ( sP4(X0,X3,X1,X2)
        | ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ sP3(X1,X3,X0) )
          & ( sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f4316,plain,
    ( ! [X1] :
        ( ~ sP3(k1_xboole_0,X1,sK7)
        | ~ r2_hidden(X1,u1_struct_0(sK7)) )
    | ~ spl13_19
    | ~ spl13_27 ),
    inference(subsumption_resolution,[],[f4313,f643])).

fof(f643,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f642])).

fof(f4313,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_struct_0(sK7))
        | ~ sP3(k1_xboole_0,X1,sK7)
        | r2_hidden(X1,k1_xboole_0) )
    | ~ spl13_27 ),
    inference(resolution,[],[f846,f488])).

fof(f488,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ sP5(X5,X6,X4)
      | ~ r2_hidden(X3,u1_struct_0(X4))
      | ~ sP3(X6,X3,X4)
      | r2_hidden(X3,X5) ) ),
    inference(resolution,[],[f115,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X2,X1,X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f115,plain,(
    ! [X4,X2,X0,X1] :
      ( sP4(X2,X4,X1,X0)
      | ~ r2_hidden(X4,u1_struct_0(X2))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f846,plain,
    ( sP5(k1_xboole_0,k1_xboole_0,sK7)
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f845])).

fof(f4306,plain,
    ( ~ spl13_21
    | spl13_27 ),
    inference(avatar_contradiction_clause,[],[f4305])).

fof(f4305,plain,
    ( $false
    | ~ spl13_21
    | spl13_27 ),
    inference(subsumption_resolution,[],[f4304,f82])).

fof(f4304,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl13_21
    | spl13_27 ),
    inference(subsumption_resolution,[],[f4302,f718])).

fof(f4302,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK7)
    | ~ l1_pre_topc(sK7)
    | spl13_27 ),
    inference(resolution,[],[f847,f857])).

fof(f857,plain,(
    ! [X8] :
      ( sP5(k1_xboole_0,k1_xboole_0,X8)
      | ~ v4_pre_topc(k1_xboole_0,X8)
      | ~ l1_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f615,f835])).

fof(f835,plain,(
    ! [X1] :
      ( sP6(X1,k1_xboole_0,k1_xboole_0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f799,f90])).

fof(f799,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | sP6(X2,X3,k1_xboole_0)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f127,f90])).

fof(f615,plain,(
    ! [X8] :
      ( ~ sP6(X8,k1_xboole_0,k1_xboole_0)
      | sP5(k1_xboole_0,k1_xboole_0,X8)
      | ~ v4_pre_topc(k1_xboole_0,X8)
      | ~ l1_pre_topc(X8) ) ),
    inference(superposition,[],[f141,f596])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ sP6(X0,X1,k2_pre_topc(X0,X1))
      | sP5(k2_pre_topc(X0,X1),X1,X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X1,X0)
      | k2_pre_topc(X0,X1) != X2
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f847,plain,
    ( ~ sP5(k1_xboole_0,k1_xboole_0,sK7)
    | spl13_27 ),
    inference(avatar_component_clause,[],[f845])).

fof(f4215,plain,
    ( spl13_15
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f4214,f143,f473])).

fof(f143,plain,
    ( spl13_1
  <=> v1_tops_1(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f4214,plain,
    ( ! [X10] : sP3(sK8,X10,sK7)
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f4213,f82])).

fof(f4213,plain,
    ( ! [X10] :
        ( ~ l1_pre_topc(sK7)
        | sP3(sK8,X10,sK7) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f4193,f144])).

fof(f144,plain,
    ( v1_tops_1(sK8,sK7)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f4193,plain,(
    ! [X10] :
      ( ~ v1_tops_1(sK8,sK7)
      | ~ l1_pre_topc(sK7)
      | sP3(sK8,X10,sK7) ) ),
    inference(resolution,[],[f83,f3144])).

fof(f3144,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_tops_1(X1,X2)
      | ~ l1_pre_topc(X2)
      | sP3(X1,X3,X2) ) ),
    inference(subsumption_resolution,[],[f3139,f887])).

fof(f887,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(X1,u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f883])).

fof(f883,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(X1,u1_struct_0(X2))
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f456,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK12(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f456,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X9,sK12(X6,X7,X8))
      | sP3(X6,X7,X8)
      | r2_hidden(X9,u1_struct_0(X8)) ) ),
    inference(resolution,[],[f123,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f3139,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_tops_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ r2_hidden(X3,u1_struct_0(X2))
      | sP3(X1,X3,X2) ) ),
    inference(resolution,[],[f1902,f1007])).

fof(f1007,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ sP5(X9,X10,X8)
      | ~ r2_hidden(X7,X9)
      | sP3(X10,X7,X8) ) ),
    inference(subsumption_resolution,[],[f489,f887])).

fof(f489,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r2_hidden(X7,u1_struct_0(X8))
      | ~ sP5(X9,X10,X8)
      | ~ r2_hidden(X7,X9)
      | sP3(X10,X7,X8) ) ),
    inference(resolution,[],[f115,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ r2_hidden(X1,X3)
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f1902,plain,(
    ! [X4,X5] :
      ( sP5(u1_struct_0(X4),X5,X4)
      | ~ v1_tops_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f1901,f798])).

fof(f798,plain,(
    ! [X0,X1] :
      ( sP6(X0,X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f127,f170])).

fof(f170,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f89,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1901,plain,(
    ! [X4,X5] :
      ( ~ sP6(X4,X5,u1_struct_0(X4))
      | sP5(u1_struct_0(X4),X5,X4)
      | ~ v1_tops_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(subsumption_resolution,[],[f1896,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1896,plain,(
    ! [X4,X5] :
      ( ~ sP6(X4,X5,u1_struct_0(X4))
      | sP5(u1_struct_0(X4),X5,X4)
      | ~ v1_tops_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ l1_struct_0(X4) ) ),
    inference(superposition,[],[f660,f94])).

fof(f94,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f660,plain,(
    ! [X12,X13] :
      ( ~ sP6(X12,X13,k2_struct_0(X12))
      | sP5(k2_struct_0(X12),X13,X12)
      | ~ v1_tops_1(X13,X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f141,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f83,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f57])).

fof(f2455,plain,
    ( spl13_1
    | ~ spl13_29
    | ~ spl13_36 ),
    inference(avatar_contradiction_clause,[],[f2454])).

fof(f2454,plain,
    ( $false
    | spl13_1
    | ~ spl13_29
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f2452,f1540])).

fof(f1540,plain,
    ( l1_struct_0(sK7)
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f1539])).

fof(f1539,plain,
    ( spl13_36
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f2452,plain,
    ( ~ l1_struct_0(sK7)
    | spl13_1
    | ~ spl13_29 ),
    inference(trivial_inequality_removal,[],[f2451])).

fof(f2451,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | ~ l1_struct_0(sK7)
    | spl13_1
    | ~ spl13_29 ),
    inference(superposition,[],[f2317,f94])).

fof(f2317,plain,
    ( u1_struct_0(sK7) != k2_struct_0(sK7)
    | spl13_1
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f2316,f82])).

fof(f2316,plain,
    ( u1_struct_0(sK7) != k2_struct_0(sK7)
    | ~ l1_pre_topc(sK7)
    | spl13_1
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f2315,f83])).

fof(f2315,plain,
    ( u1_struct_0(sK7) != k2_struct_0(sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | spl13_1
    | ~ spl13_29 ),
    inference(subsumption_resolution,[],[f2312,f1457])).

fof(f1457,plain,
    ( sP5(u1_struct_0(sK7),sK8,sK7)
    | ~ spl13_29 ),
    inference(avatar_component_clause,[],[f1455])).

fof(f1455,plain,
    ( spl13_29
  <=> sP5(u1_struct_0(sK7),sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f2312,plain,
    ( ~ sP5(u1_struct_0(sK7),sK8,sK7)
    | u1_struct_0(sK7) != k2_struct_0(sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ l1_pre_topc(sK7)
    | spl13_1 ),
    inference(resolution,[],[f2309,f798])).

fof(f2309,plain,
    ( ! [X4] :
        ( ~ sP6(sK7,sK8,X4)
        | ~ sP5(X4,sK8,sK7)
        | k2_struct_0(sK7) != X4 )
    | spl13_1 ),
    inference(subsumption_resolution,[],[f2308,f82])).

fof(f2308,plain,
    ( ! [X4] :
        ( k2_struct_0(sK7) != X4
        | ~ l1_pre_topc(sK7)
        | ~ sP5(X4,sK8,sK7)
        | ~ sP6(sK7,sK8,X4) )
    | spl13_1 ),
    inference(subsumption_resolution,[],[f2303,f145])).

fof(f145,plain,
    ( ~ v1_tops_1(sK8,sK7)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2303,plain,(
    ! [X4] :
      ( v1_tops_1(sK8,sK7)
      | k2_struct_0(sK7) != X4
      | ~ l1_pre_topc(sK7)
      | ~ sP5(X4,sK8,sK7)
      | ~ sP6(sK7,sK8,X4) ) ),
    inference(resolution,[],[f682,f83])).

fof(f682,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v1_tops_1(X3,X2)
      | k2_struct_0(X2) != X4
      | ~ l1_pre_topc(X2)
      | ~ sP5(X4,X3,X2)
      | ~ sP6(X2,X3,X4) ) ),
    inference(superposition,[],[f99,f114])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2133,plain,
    ( ~ spl13_21
    | ~ spl13_63 ),
    inference(avatar_contradiction_clause,[],[f2132])).

fof(f2132,plain,
    ( $false
    | ~ spl13_21
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f2131,f82])).

fof(f2131,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl13_21
    | ~ spl13_63 ),
    inference(resolution,[],[f2090,f718])).

fof(f2090,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(k1_xboole_0,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl13_63 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl13_63
  <=> ! [X0] :
        ( ~ v4_pre_topc(k1_xboole_0,X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f2128,plain,
    ( spl13_63
    | ~ spl13_65 ),
    inference(avatar_split_clause,[],[f2124,f2111,f2089])).

fof(f2111,plain,
    ( spl13_65
  <=> ! [X4] :
        ( ~ l1_pre_topc(X4)
        | ~ v3_pre_topc(u1_struct_0(X4),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f2124,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(k1_xboole_0,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl13_65 ),
    inference(subsumption_resolution,[],[f762,f2112])).

fof(f2112,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(u1_struct_0(X4),X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl13_65 ),
    inference(avatar_component_clause,[],[f2111])).

fof(f762,plain,(
    ! [X3] :
      ( v3_pre_topc(u1_struct_0(X3),X3)
      | ~ v4_pre_topc(k1_xboole_0,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f756,f90])).

fof(f756,plain,(
    ! [X3] :
      ( v3_pre_topc(u1_struct_0(X3),X3)
      | ~ v4_pre_topc(k1_xboole_0,X3)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f100,f373])).

fof(f373,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(subsumption_resolution,[],[f363,f170])).

fof(f363,plain,(
    ! [X1] :
      ( k3_subset_1(X1,k1_xboole_0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f234,f200])).

fof(f200,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f137,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f91,f130])).

fof(f130,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f234,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f132,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f132,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f2113,plain,
    ( spl13_65
    | spl13_19 ),
    inference(avatar_split_clause,[],[f2109,f642,f2111])).

fof(f2109,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ l1_pre_topc(X4)
      | ~ v3_pre_topc(u1_struct_0(X4),X4) ) ),
    inference(subsumption_resolution,[],[f2108,f206])).

fof(f206,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f133,f90])).

fof(f2108,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ l1_pre_topc(X4)
      | ~ v3_pre_topc(u1_struct_0(X4),X4)
      | ~ r2_hidden(X3,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f2101,f262])).

fof(f262,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f139,f247])).

fof(f247,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f235,f200])).

fof(f235,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f138,f92])).

fof(f138,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f129,f130,f130])).

fof(f129,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f139,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f135,f130])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2101,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ l1_pre_topc(X4)
      | ~ v3_pre_topc(u1_struct_0(X4),X4)
      | ~ r1_xboole_0(k1_xboole_0,u1_struct_0(X4))
      | ~ r2_hidden(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f647,f849])).

fof(f849,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X0,X1)
      | ~ v3_pre_topc(u1_struct_0(X1),X1)
      | ~ r1_xboole_0(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f107,f170])).

fof(f647,plain,(
    ! [X0,X1] :
      ( sP0(k1_xboole_0,X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f646,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | v2_struct_0(X0) )
      & ( ( sP0(X2,X1,X0)
          & ~ v2_struct_0(X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0,X2,X1] :
      ( ( sP1(X0,X2,X1)
        | ~ sP0(X1,X2,X0)
        | v2_struct_0(X0) )
      & ( ( sP0(X1,X2,X0)
          & ~ v2_struct_0(X0) )
        | ~ sP1(X0,X2,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X2,X1] :
      ( ( sP1(X0,X2,X1)
        | ~ sP0(X1,X2,X0)
        | v2_struct_0(X0) )
      & ( ( sP0(X1,X2,X0)
          & ~ v2_struct_0(X0) )
        | ~ sP1(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( sP1(X0,X2,X1)
    <=> ( sP0(X1,X2,X0)
        & ~ v2_struct_0(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f646,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0,k1_xboole_0)
      | ~ l1_pre_topc(X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f645,f209])).

fof(f209,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f136,f90])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f645,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | sP1(X1,X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f628,f478])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X2,X1,X0)
      | sP1(X0,X1,X2)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f102,f206])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X2,X0))
      | sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k2_pre_topc(X2,X0))
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_hidden(X1,k2_pre_topc(X2,X0)) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
          | ~ sP1(X0,X2,X1) )
        & ( sP1(X0,X2,X1)
          | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
      | ~ sP2(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
      <=> sP1(X0,X2,X1) )
      | ~ sP2(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f628,plain,(
    ! [X2,X3] :
      ( sP2(k1_xboole_0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f112,f90])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP2(X1,X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X1,X2,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f32,f44,f43,f42])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & ~ v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_xboole_0(X1,X3)
                          & r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) ) )
                  & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(f1963,plain,
    ( spl13_15
    | ~ spl13_6
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f671,f642,f167,f473])).

fof(f167,plain,
    ( spl13_6
  <=> ! [X3] :
        ( ~ r1_xboole_0(sK8,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f671,plain,
    ( ! [X4] : sP3(sK8,X4,sK7)
    | ~ spl13_6
    | ~ spl13_19 ),
    inference(subsumption_resolution,[],[f468,f643])).

fof(f468,plain,
    ( ! [X4] :
        ( sP3(sK8,X4,sK7)
        | r2_hidden(X4,k1_xboole_0) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k1_xboole_0)
        | sP3(sK8,X4,sK7)
        | sP3(sK8,X4,sK7) )
    | ~ spl13_6 ),
    inference(superposition,[],[f125,f460])).

fof(f460,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK12(sK8,X0,sK7)
        | sP3(sK8,X0,sK7) )
    | ~ spl13_6 ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( ! [X0] :
        ( sP3(sK8,X0,sK7)
        | k1_xboole_0 = sK12(sK8,X0,sK7)
        | sP3(sK8,X0,sK7) )
    | ~ spl13_6 ),
    inference(resolution,[],[f457,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,sK12(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f457,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(sK8,sK12(X0,X1,sK7))
        | sP3(X0,X1,sK7)
        | k1_xboole_0 = sK12(X0,X1,sK7) )
    | ~ spl13_6 ),
    inference(subsumption_resolution,[],[f454,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK12(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f454,plain,
    ( ! [X0,X1] :
        ( sP3(X0,X1,sK7)
        | ~ r1_xboole_0(sK8,sK12(X0,X1,sK7))
        | k1_xboole_0 = sK12(X0,X1,sK7)
        | ~ v3_pre_topc(sK12(X0,X1,sK7),sK7) )
    | ~ spl13_6 ),
    inference(resolution,[],[f123,f168])).

fof(f168,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))
        | ~ r1_xboole_0(sK8,X3)
        | k1_xboole_0 = X3
        | ~ v3_pre_topc(X3,sK7) )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1549,plain,(
    spl13_36 ),
    inference(avatar_contradiction_clause,[],[f1548])).

fof(f1548,plain,
    ( $false
    | spl13_36 ),
    inference(subsumption_resolution,[],[f1547,f82])).

fof(f1547,plain,
    ( ~ l1_pre_topc(sK7)
    | spl13_36 ),
    inference(resolution,[],[f1541,f95])).

fof(f1541,plain,
    ( ~ l1_struct_0(sK7)
    | spl13_36 ),
    inference(avatar_component_clause,[],[f1539])).

fof(f1459,plain,
    ( spl13_29
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f1449,f473,f1455])).

fof(f1449,plain,
    ( sP5(u1_struct_0(sK7),sK8,sK7)
    | ~ spl13_15 ),
    inference(duplicate_literal_removal,[],[f1445])).

fof(f1445,plain,
    ( sP5(u1_struct_0(sK7),sK8,sK7)
    | sP5(u1_struct_0(sK7),sK8,sK7)
    | ~ spl13_15 ),
    inference(resolution,[],[f1437,f116])).

fof(f1437,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK11(X0,sK8,sK7),X0)
        | sP5(X0,sK8,sK7) )
    | ~ spl13_15 ),
    inference(resolution,[],[f449,f474])).

fof(f449,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,sK11(X1,X0,X2),X2)
      | ~ r2_hidden(sK11(X1,X0,X2),X1)
      | sP5(X1,X0,X2) ) ),
    inference(resolution,[],[f121,f117])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | ~ sP3(X2,X1,X0)
      | ~ r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f792,plain,(
    spl13_21 ),
    inference(avatar_contradiction_clause,[],[f791])).

fof(f791,plain,
    ( $false
    | spl13_21 ),
    inference(subsumption_resolution,[],[f790,f81])).

fof(f81,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f790,plain,
    ( ~ v2_pre_topc(sK7)
    | spl13_21 ),
    inference(subsumption_resolution,[],[f789,f82])).

fof(f789,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7)
    | spl13_21 ),
    inference(resolution,[],[f787,f719])).

fof(f719,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK7)
    | spl13_21 ),
    inference(avatar_component_clause,[],[f717])).

fof(f787,plain,(
    ! [X1] :
      ( v4_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,(
    ! [X1] :
      ( v4_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f778,f202])).

fof(f202,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f201,f95])).

fof(f201,plain,(
    ! [X0] :
      ( v3_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f128,f94])).

fof(f128,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f778,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),X3)
      | v4_pre_topc(k1_xboole_0,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f771,f90])).

fof(f771,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(u1_struct_0(X3),X3)
      | v4_pre_topc(k1_xboole_0,X3)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f101,f373])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f169,plain,
    ( spl13_1
    | spl13_6 ),
    inference(avatar_split_clause,[],[f84,f167,f143])).

fof(f84,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK8,X3)
      | ~ v3_pre_topc(X3,sK7)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))
      | v1_tops_1(sK8,sK7) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f165,plain,
    ( ~ spl13_1
    | spl13_5 ),
    inference(avatar_split_clause,[],[f85,f162,f143])).

fof(f85,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ v1_tops_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f160,plain,
    ( ~ spl13_1
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f86,f157,f143])).

fof(f86,plain,
    ( k1_xboole_0 != sK9
    | ~ v1_tops_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f155,plain,
    ( ~ spl13_1
    | spl13_3 ),
    inference(avatar_split_clause,[],[f87,f152,f143])).

fof(f87,plain,
    ( v3_pre_topc(sK9,sK7)
    | ~ v1_tops_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f150,plain,
    ( ~ spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f88,f147,f143])).

fof(f88,plain,
    ( r1_xboole_0(sK8,sK9)
    | ~ v1_tops_1(sK8,sK7) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:30:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (23768)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (23742)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (23755)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (23744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23765)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (23760)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (23762)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (23744)Refutation not found, incomplete strategy% (23744)------------------------------
% 0.22/0.53  % (23744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23747)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (23764)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (23744)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23744)Memory used [KB]: 10874
% 0.22/0.53  % (23749)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (23744)Time elapsed: 0.100 s
% 0.22/0.53  % (23744)------------------------------
% 0.22/0.53  % (23744)------------------------------
% 0.22/0.54  % (23746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23756)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (23745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (23771)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (23748)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (23757)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (23743)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23750)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (23767)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (23768)Refutation not found, incomplete strategy% (23768)------------------------------
% 0.22/0.54  % (23768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23768)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23768)Memory used [KB]: 10874
% 0.22/0.54  % (23768)Time elapsed: 0.130 s
% 0.22/0.54  % (23768)------------------------------
% 0.22/0.54  % (23768)------------------------------
% 0.22/0.54  % (23770)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (23758)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (23763)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (23750)Refutation not found, incomplete strategy% (23750)------------------------------
% 0.22/0.55  % (23750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23750)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23750)Memory used [KB]: 10874
% 0.22/0.55  % (23750)Time elapsed: 0.126 s
% 0.22/0.55  % (23750)------------------------------
% 0.22/0.55  % (23750)------------------------------
% 0.22/0.55  % (23751)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (23759)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (23766)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (23759)Refutation not found, incomplete strategy% (23759)------------------------------
% 0.22/0.55  % (23759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23759)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23759)Memory used [KB]: 10746
% 0.22/0.55  % (23759)Time elapsed: 0.136 s
% 0.22/0.55  % (23759)------------------------------
% 0.22/0.55  % (23759)------------------------------
% 0.22/0.55  % (23761)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (23752)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (23754)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (23753)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.56  % (23764)Refutation not found, incomplete strategy% (23764)------------------------------
% 1.53/0.56  % (23764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (23764)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (23764)Memory used [KB]: 10874
% 1.53/0.56  % (23764)Time elapsed: 0.107 s
% 1.53/0.56  % (23764)------------------------------
% 1.53/0.56  % (23764)------------------------------
% 1.53/0.57  % (23769)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.59  % (23752)Refutation not found, incomplete strategy% (23752)------------------------------
% 1.53/0.59  % (23752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (23752)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.59  
% 1.53/0.59  % (23752)Memory used [KB]: 11001
% 1.53/0.59  % (23752)Time elapsed: 0.156 s
% 1.53/0.59  % (23752)------------------------------
% 1.53/0.59  % (23752)------------------------------
% 2.16/0.67  % (23826)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.69  % (23836)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.16/0.70  % (23819)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.16/0.70  % (23832)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.57/0.71  % (23823)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.57/0.73  % (23846)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.90/0.83  % (23747)Time limit reached!
% 2.90/0.83  % (23747)------------------------------
% 2.90/0.83  % (23747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.85  % (23823)Refutation not found, incomplete strategy% (23823)------------------------------
% 2.90/0.85  % (23823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.85  % (23747)Termination reason: Time limit
% 2.90/0.85  
% 2.90/0.85  % (23747)Memory used [KB]: 8315
% 2.90/0.85  % (23747)Time elapsed: 0.415 s
% 2.90/0.85  % (23747)------------------------------
% 2.90/0.85  % (23747)------------------------------
% 3.50/0.85  % (23769)Refutation found. Thanks to Tanya!
% 3.50/0.85  % SZS status Theorem for theBenchmark
% 3.50/0.86  % SZS output start Proof for theBenchmark
% 3.50/0.86  fof(f4551,plain,(
% 3.50/0.86    $false),
% 3.50/0.86    inference(avatar_sat_refutation,[],[f150,f155,f160,f165,f169,f792,f1459,f1549,f1963,f2113,f2128,f2133,f2455,f4215,f4306,f4524,f4536,f4544])).
% 3.50/0.86  fof(f4544,plain,(
% 3.50/0.86    spl13_13 | ~spl13_15),
% 3.50/0.86    inference(avatar_split_clause,[],[f3131,f473,f316])).
% 3.50/0.86  fof(f316,plain,(
% 3.50/0.86    spl13_13 <=> ! [X5] : sP0(sK8,X5,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 3.50/0.86  fof(f473,plain,(
% 3.50/0.86    spl13_15 <=> ! [X5] : sP3(sK8,X5,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 3.50/0.86  fof(f3131,plain,(
% 3.50/0.86    ( ! [X15] : (sP0(sK8,X15,sK7)) ) | ~spl13_15),
% 3.50/0.86    inference(resolution,[],[f3049,f474])).
% 3.50/0.86  fof(f474,plain,(
% 3.50/0.86    ( ! [X5] : (sP3(sK8,X5,sK7)) ) | ~spl13_15),
% 3.50/0.86    inference(avatar_component_clause,[],[f473])).
% 3.50/0.86  fof(f3049,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(duplicate_literal_removal,[],[f3041])).
% 3.50/0.86  fof(f3041,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | sP0(X0,X1,X2) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(resolution,[],[f2079,f111])).
% 3.50/0.86  fof(f111,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (r1_xboole_0(X0,sK10(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f68])).
% 3.50/0.86  fof(f68,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (r1_xboole_0(X0,sK10(X0,X1,X2)) & r2_hidden(X1,sK10(X0,X1,X2)) & v3_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (~r1_xboole_0(X0,X4) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 3.50/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f66,f67])).
% 3.50/0.86  fof(f67,plain,(
% 3.50/0.86    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X0,X3) & r2_hidden(X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (r1_xboole_0(X0,sK10(X0,X1,X2)) & r2_hidden(X1,sK10(X0,X1,X2)) & v3_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f66,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (r1_xboole_0(X0,X3) & r2_hidden(X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (~r1_xboole_0(X0,X4) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 3.50/0.86    inference(rectify,[],[f65])).
% 3.50/0.86  fof(f65,plain,(
% 3.50/0.86    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 3.50/0.86    inference(nnf_transformation,[],[f42])).
% 3.50/0.86  fof(f42,plain,(
% 3.50/0.86    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.50/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.50/0.86  fof(f2079,plain,(
% 3.50/0.86    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,sK10(X1,X2,X3)) | ~sP3(X0,X2,X3) | sP0(X1,X2,X3)) )),
% 3.50/0.86    inference(duplicate_literal_removal,[],[f2077])).
% 3.50/0.86  fof(f2077,plain,(
% 3.50/0.86    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,sK10(X1,X2,X3)) | ~sP3(X0,X2,X3) | sP0(X1,X2,X3) | sP0(X1,X2,X3)) )),
% 3.50/0.86    inference(resolution,[],[f874,f110])).
% 3.50/0.86  fof(f110,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (r2_hidden(X1,sK10(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f68])).
% 3.50/0.86  fof(f874,plain,(
% 3.50/0.86    ( ! [X12,X10,X8,X11,X9] : (~r2_hidden(X8,sK10(X9,X10,X11)) | ~r1_xboole_0(X12,sK10(X9,X10,X11)) | ~sP3(X12,X8,X11) | sP0(X9,X10,X11)) )),
% 3.50/0.86    inference(subsumption_resolution,[],[f871,f109])).
% 3.50/0.86  fof(f109,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (v3_pre_topc(sK10(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f68])).
% 3.50/0.86  fof(f871,plain,(
% 3.50/0.86    ( ! [X12,X10,X8,X11,X9] : (~r2_hidden(X8,sK10(X9,X10,X11)) | ~v3_pre_topc(sK10(X9,X10,X11),X11) | ~r1_xboole_0(X12,sK10(X9,X10,X11)) | ~sP3(X12,X8,X11) | sP0(X9,X10,X11)) )),
% 3.50/0.86    inference(resolution,[],[f122,f108])).
% 3.50/0.86  fof(f108,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f68])).
% 3.50/0.86  fof(f122,plain,(
% 3.50/0.86    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~r1_xboole_0(X0,X4) | ~sP3(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f79])).
% 3.50/0.86  fof(f79,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (r1_xboole_0(X0,sK12(X0,X1,X2)) & r2_hidden(X1,sK12(X0,X1,X2)) & v3_pre_topc(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (~r1_xboole_0(X0,X4) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP3(X0,X1,X2)))),
% 3.50/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f77,f78])).
% 3.50/0.86  fof(f78,plain,(
% 3.50/0.86    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X0,X3) & r2_hidden(X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (r1_xboole_0(X0,sK12(X0,X1,X2)) & r2_hidden(X1,sK12(X0,X1,X2)) & v3_pre_topc(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f77,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (r1_xboole_0(X0,X3) & r2_hidden(X1,X3) & v3_pre_topc(X3,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (! [X4] : (~r1_xboole_0(X0,X4) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP3(X0,X1,X2)))),
% 3.50/0.86    inference(rectify,[],[f76])).
% 3.50/0.86  fof(f76,plain,(
% 3.50/0.86    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | ? [X4] : (r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X1,X3,X0)))),
% 3.50/0.86    inference(nnf_transformation,[],[f46])).
% 3.50/0.86  fof(f46,plain,(
% 3.50/0.86    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.50/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.50/0.86  fof(f4536,plain,(
% 3.50/0.86    ~spl13_76 | spl13_4 | ~spl13_5 | ~spl13_21),
% 3.50/0.86    inference(avatar_split_clause,[],[f2398,f717,f162,f157,f2400])).
% 3.50/0.86  fof(f2400,plain,(
% 3.50/0.86    spl13_76 <=> sP5(sK9,k1_xboole_0,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).
% 3.50/0.86  fof(f157,plain,(
% 3.50/0.86    spl13_4 <=> k1_xboole_0 = sK9),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 3.50/0.86  fof(f162,plain,(
% 3.50/0.86    spl13_5 <=> m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 3.50/0.86  fof(f717,plain,(
% 3.50/0.86    spl13_21 <=> v4_pre_topc(k1_xboole_0,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).
% 3.50/0.86  fof(f2398,plain,(
% 3.50/0.86    ~sP5(sK9,k1_xboole_0,sK7) | (spl13_4 | ~spl13_5 | ~spl13_21)),
% 3.50/0.86    inference(subsumption_resolution,[],[f2397,f159])).
% 3.50/0.86  fof(f159,plain,(
% 3.50/0.86    k1_xboole_0 != sK9 | spl13_4),
% 3.50/0.86    inference(avatar_component_clause,[],[f157])).
% 3.50/0.86  fof(f2397,plain,(
% 3.50/0.86    ~sP5(sK9,k1_xboole_0,sK7) | k1_xboole_0 = sK9 | (~spl13_5 | ~spl13_21)),
% 3.50/0.86    inference(subsumption_resolution,[],[f2396,f82])).
% 3.50/0.86  fof(f82,plain,(
% 3.50/0.86    l1_pre_topc(sK7)),
% 3.50/0.86    inference(cnf_transformation,[],[f57])).
% 3.50/0.86  fof(f57,plain,(
% 3.50/0.86    (((r1_xboole_0(sK8,sK9) & v3_pre_topc(sK9,sK7) & k1_xboole_0 != sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))) | ~v1_tops_1(sK8,sK7)) & (! [X3] : (~r1_xboole_0(sK8,X3) | ~v3_pre_topc(X3,sK7) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) | v1_tops_1(sK8,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))) & l1_pre_topc(sK7) & v2_pre_topc(sK7)),
% 3.50/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f53,f56,f55,f54])).
% 3.50/0.86  fof(f54,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK7) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))) | ~v1_tops_1(X1,sK7)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK7) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) | v1_tops_1(X1,sK7)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))) & l1_pre_topc(sK7) & v2_pre_topc(sK7))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f55,plain,(
% 3.50/0.86    ? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,sK7) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))) | ~v1_tops_1(X1,sK7)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,sK7) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) | v1_tops_1(X1,sK7)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))) => ((? [X2] : (r1_xboole_0(sK8,X2) & v3_pre_topc(X2,sK7) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))) | ~v1_tops_1(sK8,sK7)) & (! [X3] : (~r1_xboole_0(sK8,X3) | ~v3_pre_topc(X3,sK7) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) | v1_tops_1(sK8,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f56,plain,(
% 3.50/0.86    ? [X2] : (r1_xboole_0(sK8,X2) & v3_pre_topc(X2,sK7) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))) => (r1_xboole_0(sK8,sK9) & v3_pre_topc(sK9,sK7) & k1_xboole_0 != sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f53,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.50/0.86    inference(rectify,[],[f52])).
% 3.50/0.86  fof(f52,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : ((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.50/0.86    inference(flattening,[],[f51])).
% 3.50/0.86  fof(f51,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : (((? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.50/0.86    inference(nnf_transformation,[],[f24])).
% 3.50/0.86  fof(f24,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.50/0.86    inference(flattening,[],[f23])).
% 3.50/0.86  fof(f23,plain,(
% 3.50/0.86    ? [X0] : (? [X1] : ((v1_tops_1(X1,X0) <~> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.50/0.86    inference(ennf_transformation,[],[f22])).
% 3.50/0.86  fof(f22,negated_conjecture,(
% 3.50/0.86    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 3.50/0.86    inference(negated_conjecture,[],[f21])).
% 3.50/0.86  fof(f21,conjecture,(
% 3.50/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 3.50/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).
% 3.50/0.86  fof(f2396,plain,(
% 3.50/0.86    ~l1_pre_topc(sK7) | ~sP5(sK9,k1_xboole_0,sK7) | k1_xboole_0 = sK9 | (~spl13_5 | ~spl13_21)),
% 3.50/0.86    inference(subsumption_resolution,[],[f2392,f718])).
% 3.50/0.86  fof(f718,plain,(
% 3.50/0.86    v4_pre_topc(k1_xboole_0,sK7) | ~spl13_21),
% 3.50/0.86    inference(avatar_component_clause,[],[f717])).
% 3.50/0.86  fof(f2392,plain,(
% 3.50/0.86    ~v4_pre_topc(k1_xboole_0,sK7) | ~l1_pre_topc(sK7) | ~sP5(sK9,k1_xboole_0,sK7) | k1_xboole_0 = sK9 | ~spl13_5),
% 3.50/0.86    inference(resolution,[],[f1599,f610])).
% 3.50/0.86  fof(f610,plain,(
% 3.50/0.86    ( ! [X2,X1] : (~sP6(X1,k1_xboole_0,X2) | ~v4_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | ~sP5(X2,k1_xboole_0,X1) | k1_xboole_0 = X2) )),
% 3.50/0.86    inference(superposition,[],[f596,f114])).
% 3.50/0.86  fof(f114,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X1) = X2 | ~sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f69])).
% 3.50/0.86  fof(f69,plain,(
% 3.50/0.86    ! [X0,X1,X2] : (((k2_pre_topc(X0,X1) = X2 | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | k2_pre_topc(X0,X1) != X2)) | ~sP6(X0,X1,X2))),
% 3.50/0.86    inference(nnf_transformation,[],[f49])).
% 3.50/0.86  fof(f49,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((k2_pre_topc(X0,X1) = X2 <=> sP5(X2,X1,X0)) | ~sP6(X0,X1,X2))),
% 3.50/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 3.50/0.86  fof(f596,plain,(
% 3.50/0.86    ( ! [X1] : (k1_xboole_0 = k2_pre_topc(X1,k1_xboole_0) | ~v4_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1)) )),
% 3.50/0.86    inference(resolution,[],[f96,f90])).
% 3.50/0.86  fof(f90,plain,(
% 3.50/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.50/0.86    inference(cnf_transformation,[],[f11])).
% 3.50/0.86  fof(f11,axiom,(
% 3.50/0.86    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.50/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.50/0.86  fof(f96,plain,(
% 3.50/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f28])).
% 3.50/0.86  fof(f28,plain,(
% 3.50/0.86    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.86    inference(flattening,[],[f27])).
% 3.50/0.86  fof(f27,plain,(
% 3.50/0.86    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.86    inference(ennf_transformation,[],[f16])).
% 3.50/0.86  fof(f16,axiom,(
% 3.50/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.50/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 3.50/0.86  fof(f1599,plain,(
% 3.50/0.86    sP6(sK7,k1_xboole_0,sK9) | ~spl13_5),
% 3.50/0.86    inference(resolution,[],[f1578,f90])).
% 3.50/0.86  fof(f1578,plain,(
% 3.50/0.86    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK7))) | sP6(sK7,X5,sK9)) ) | ~spl13_5),
% 3.50/0.86    inference(subsumption_resolution,[],[f1557,f82])).
% 3.50/0.86  fof(f1557,plain,(
% 3.50/0.86    ( ! [X5] : (sP6(sK7,X5,sK9) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK7))) | ~l1_pre_topc(sK7)) ) | ~spl13_5),
% 3.50/0.86    inference(resolution,[],[f164,f127])).
% 3.50/0.86  fof(f127,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP6(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f50])).
% 3.50/0.86  fof(f50,plain,(
% 3.50/0.86    ! [X0] : (! [X1] : (! [X2] : (sP6(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.86    inference(definition_folding,[],[f34,f49,f48,f47,f46])).
% 3.50/0.86  fof(f47,plain,(
% 3.50/0.86    ! [X0,X3,X1,X2] : (sP4(X0,X3,X1,X2) <=> (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 3.50/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.50/0.86  fof(f48,plain,(
% 3.50/0.86    ! [X2,X1,X0] : (sP5(X2,X1,X0) <=> ! [X3] : (sP4(X0,X3,X1,X2) | ~r2_hidden(X3,u1_struct_0(X0))))),
% 3.50/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 3.50/0.86  fof(f34,plain,(
% 3.50/0.86    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.86    inference(flattening,[],[f33])).
% 3.50/0.86  fof(f33,plain,(
% 3.50/0.86    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : ((~r1_xboole_0(X1,X4) | ~r2_hidden(X3,X4) | ~v3_pre_topc(X4,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.86    inference(ennf_transformation,[],[f13])).
% 3.50/0.86  fof(f13,axiom,(
% 3.50/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k2_pre_topc(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X4) & r2_hidden(X3,X4) & v3_pre_topc(X4,X0)))))))))),
% 3.50/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_pre_topc)).
% 3.50/0.86  fof(f164,plain,(
% 3.50/0.86    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) | ~spl13_5),
% 3.50/0.86    inference(avatar_component_clause,[],[f162])).
% 3.50/0.86  fof(f4524,plain,(
% 3.50/0.86    spl13_76 | ~spl13_2 | ~spl13_3 | ~spl13_5 | ~spl13_13 | ~spl13_19 | ~spl13_27),
% 3.50/0.86    inference(avatar_split_clause,[],[f4513,f845,f642,f316,f162,f152,f147,f2400])).
% 3.50/0.86  fof(f147,plain,(
% 3.50/0.86    spl13_2 <=> r1_xboole_0(sK8,sK9)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 3.50/0.86  fof(f152,plain,(
% 3.50/0.86    spl13_3 <=> v3_pre_topc(sK9,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 3.50/0.86  fof(f642,plain,(
% 3.50/0.86    spl13_19 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 3.50/0.86  fof(f845,plain,(
% 3.50/0.86    spl13_27 <=> sP5(k1_xboole_0,k1_xboole_0,sK7)),
% 3.50/0.86    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).
% 3.50/0.86  fof(f4513,plain,(
% 3.50/0.86    sP5(sK9,k1_xboole_0,sK7) | (~spl13_2 | ~spl13_3 | ~spl13_5 | ~spl13_13 | ~spl13_19 | ~spl13_27)),
% 3.50/0.86    inference(resolution,[],[f4401,f1611])).
% 3.50/0.86  fof(f1611,plain,(
% 3.50/0.86    ( ! [X0] : (~r2_hidden(X0,sK9)) ) | (~spl13_2 | ~spl13_3 | ~spl13_5 | ~spl13_13)),
% 3.50/0.86    inference(subsumption_resolution,[],[f1608,f149])).
% 3.50/0.86  fof(f149,plain,(
% 3.50/0.86    r1_xboole_0(sK8,sK9) | ~spl13_2),
% 3.50/0.86    inference(avatar_component_clause,[],[f147])).
% 3.50/0.86  fof(f1608,plain,(
% 3.50/0.86    ( ! [X0] : (~r1_xboole_0(sK8,sK9) | ~r2_hidden(X0,sK9)) ) | (~spl13_3 | ~spl13_5 | ~spl13_13)),
% 3.50/0.86    inference(resolution,[],[f1575,f317])).
% 3.50/0.86  fof(f317,plain,(
% 3.50/0.86    ( ! [X5] : (sP0(sK8,X5,sK7)) ) | ~spl13_13),
% 3.50/0.86    inference(avatar_component_clause,[],[f316])).
% 3.50/0.86  fof(f1575,plain,(
% 3.50/0.86    ( ! [X0,X1] : (~sP0(X1,X0,sK7) | ~r1_xboole_0(X1,sK9) | ~r2_hidden(X0,sK9)) ) | (~spl13_3 | ~spl13_5)),
% 3.50/0.86    inference(subsumption_resolution,[],[f1554,f154])).
% 3.50/0.86  fof(f154,plain,(
% 3.50/0.86    v3_pre_topc(sK9,sK7) | ~spl13_3),
% 3.50/0.86    inference(avatar_component_clause,[],[f152])).
% 3.50/0.86  fof(f1554,plain,(
% 3.50/0.86    ( ! [X0,X1] : (~r2_hidden(X0,sK9) | ~v3_pre_topc(sK9,sK7) | ~r1_xboole_0(X1,sK9) | ~sP0(X1,X0,sK7)) ) | ~spl13_5),
% 3.50/0.86    inference(resolution,[],[f164,f107])).
% 3.50/0.86  fof(f107,plain,(
% 3.50/0.86    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~r2_hidden(X1,X4) | ~v3_pre_topc(X4,X2) | ~r1_xboole_0(X0,X4) | ~sP0(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f68])).
% 3.50/0.86  fof(f4401,plain,(
% 3.50/0.86    ( ! [X6] : (r2_hidden(sK11(X6,k1_xboole_0,sK7),X6) | sP5(X6,k1_xboole_0,sK7)) ) | (~spl13_19 | ~spl13_27)),
% 3.50/0.86    inference(subsumption_resolution,[],[f4400,f116])).
% 3.50/0.86  fof(f116,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2)) | sP5(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f73])).
% 3.50/0.86  fof(f73,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~sP4(X2,sK11(X0,X1,X2),X1,X0) & r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2)))) & (! [X4] : (sP4(X2,X4,X1,X0) | ~r2_hidden(X4,u1_struct_0(X2))) | ~sP5(X0,X1,X2)))),
% 3.50/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f71,f72])).
% 3.50/0.86  fof(f72,plain,(
% 3.50/0.86    ! [X2,X1,X0] : (? [X3] : (~sP4(X2,X3,X1,X0) & r2_hidden(X3,u1_struct_0(X2))) => (~sP4(X2,sK11(X0,X1,X2),X1,X0) & r2_hidden(sK11(X0,X1,X2),u1_struct_0(X2))))),
% 3.50/0.86    introduced(choice_axiom,[])).
% 3.50/0.86  fof(f71,plain,(
% 3.50/0.86    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~sP4(X2,X3,X1,X0) & r2_hidden(X3,u1_struct_0(X2)))) & (! [X4] : (sP4(X2,X4,X1,X0) | ~r2_hidden(X4,u1_struct_0(X2))) | ~sP5(X0,X1,X2)))),
% 3.50/0.86    inference(rectify,[],[f70])).
% 3.50/0.86  fof(f70,plain,(
% 3.50/0.86    ! [X2,X1,X0] : ((sP5(X2,X1,X0) | ? [X3] : (~sP4(X0,X3,X1,X2) & r2_hidden(X3,u1_struct_0(X0)))) & (! [X3] : (sP4(X0,X3,X1,X2) | ~r2_hidden(X3,u1_struct_0(X0))) | ~sP5(X2,X1,X0)))),
% 3.50/0.86    inference(nnf_transformation,[],[f48])).
% 3.50/0.86  fof(f4400,plain,(
% 3.50/0.86    ( ! [X6] : (~r2_hidden(sK11(X6,k1_xboole_0,sK7),u1_struct_0(sK7)) | r2_hidden(sK11(X6,k1_xboole_0,sK7),X6) | sP5(X6,k1_xboole_0,sK7)) ) | (~spl13_19 | ~spl13_27)),
% 3.50/0.86    inference(resolution,[],[f4316,f422])).
% 3.50/0.86  fof(f422,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (sP3(X0,sK11(X1,X0,X2),X2) | r2_hidden(sK11(X1,X0,X2),X1) | sP5(X1,X0,X2)) )),
% 3.50/0.86    inference(resolution,[],[f120,f117])).
% 3.50/0.86  fof(f117,plain,(
% 3.50/0.86    ( ! [X2,X0,X1] : (~sP4(X2,sK11(X0,X1,X2),X1,X0) | sP5(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f73])).
% 3.50/0.86  fof(f120,plain,(
% 3.50/0.86    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | sP3(X2,X1,X0) | r2_hidden(X1,X3)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f75])).
% 3.50/0.86  fof(f75,plain,(
% 3.50/0.86    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(X2,X1,X0) | ~r2_hidden(X1,X3)) & (sP3(X2,X1,X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X1,X3))) | ~sP4(X0,X1,X2,X3)))),
% 3.50/0.86    inference(rectify,[],[f74])).
% 3.50/0.86  fof(f74,plain,(
% 3.50/0.86    ! [X0,X3,X1,X2] : ((sP4(X0,X3,X1,X2) | ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X3,X1,X2)))),
% 3.50/0.86    inference(nnf_transformation,[],[f47])).
% 3.50/0.86  fof(f4316,plain,(
% 3.50/0.86    ( ! [X1] : (~sP3(k1_xboole_0,X1,sK7) | ~r2_hidden(X1,u1_struct_0(sK7))) ) | (~spl13_19 | ~spl13_27)),
% 3.50/0.86    inference(subsumption_resolution,[],[f4313,f643])).
% 3.50/0.86  fof(f643,plain,(
% 3.50/0.86    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl13_19),
% 3.50/0.86    inference(avatar_component_clause,[],[f642])).
% 3.50/0.86  fof(f4313,plain,(
% 3.50/0.86    ( ! [X1] : (~r2_hidden(X1,u1_struct_0(sK7)) | ~sP3(k1_xboole_0,X1,sK7) | r2_hidden(X1,k1_xboole_0)) ) | ~spl13_27),
% 3.50/0.86    inference(resolution,[],[f846,f488])).
% 3.50/0.86  fof(f488,plain,(
% 3.50/0.86    ( ! [X6,X4,X5,X3] : (~sP5(X5,X6,X4) | ~r2_hidden(X3,u1_struct_0(X4)) | ~sP3(X6,X3,X4) | r2_hidden(X3,X5)) )),
% 3.50/0.86    inference(resolution,[],[f115,f119])).
% 3.50/0.86  fof(f119,plain,(
% 3.50/0.86    ( ! [X2,X0,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X2,X1,X0) | r2_hidden(X1,X3)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f75])).
% 3.50/0.86  fof(f115,plain,(
% 3.50/0.86    ( ! [X4,X2,X0,X1] : (sP4(X2,X4,X1,X0) | ~r2_hidden(X4,u1_struct_0(X2)) | ~sP5(X0,X1,X2)) )),
% 3.50/0.86    inference(cnf_transformation,[],[f73])).
% 3.50/0.86  fof(f846,plain,(
% 3.50/0.86    sP5(k1_xboole_0,k1_xboole_0,sK7) | ~spl13_27),
% 3.50/0.86    inference(avatar_component_clause,[],[f845])).
% 3.50/0.86  fof(f4306,plain,(
% 3.50/0.86    ~spl13_21 | spl13_27),
% 3.50/0.86    inference(avatar_contradiction_clause,[],[f4305])).
% 3.50/0.86  fof(f4305,plain,(
% 3.50/0.86    $false | (~spl13_21 | spl13_27)),
% 3.50/0.86    inference(subsumption_resolution,[],[f4304,f82])).
% 3.50/0.87  fof(f4304,plain,(
% 3.50/0.87    ~l1_pre_topc(sK7) | (~spl13_21 | spl13_27)),
% 3.50/0.87    inference(subsumption_resolution,[],[f4302,f718])).
% 3.50/0.87  fof(f4302,plain,(
% 3.50/0.87    ~v4_pre_topc(k1_xboole_0,sK7) | ~l1_pre_topc(sK7) | spl13_27),
% 3.50/0.87    inference(resolution,[],[f847,f857])).
% 3.50/0.87  fof(f857,plain,(
% 3.50/0.87    ( ! [X8] : (sP5(k1_xboole_0,k1_xboole_0,X8) | ~v4_pre_topc(k1_xboole_0,X8) | ~l1_pre_topc(X8)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f615,f835])).
% 3.50/0.87  fof(f835,plain,(
% 3.50/0.87    ( ! [X1] : (sP6(X1,k1_xboole_0,k1_xboole_0) | ~l1_pre_topc(X1)) )),
% 3.50/0.87    inference(resolution,[],[f799,f90])).
% 3.50/0.87  fof(f799,plain,(
% 3.50/0.87    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | sP6(X2,X3,k1_xboole_0) | ~l1_pre_topc(X2)) )),
% 3.50/0.87    inference(resolution,[],[f127,f90])).
% 3.50/0.87  fof(f615,plain,(
% 3.50/0.87    ( ! [X8] : (~sP6(X8,k1_xboole_0,k1_xboole_0) | sP5(k1_xboole_0,k1_xboole_0,X8) | ~v4_pre_topc(k1_xboole_0,X8) | ~l1_pre_topc(X8)) )),
% 3.50/0.87    inference(superposition,[],[f141,f596])).
% 3.50/0.87  fof(f141,plain,(
% 3.50/0.87    ( ! [X0,X1] : (~sP6(X0,X1,k2_pre_topc(X0,X1)) | sP5(k2_pre_topc(X0,X1),X1,X0)) )),
% 3.50/0.87    inference(equality_resolution,[],[f113])).
% 3.50/0.87  fof(f113,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (sP5(X2,X1,X0) | k2_pre_topc(X0,X1) != X2 | ~sP6(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f69])).
% 3.50/0.87  fof(f847,plain,(
% 3.50/0.87    ~sP5(k1_xboole_0,k1_xboole_0,sK7) | spl13_27),
% 3.50/0.87    inference(avatar_component_clause,[],[f845])).
% 3.50/0.87  fof(f4215,plain,(
% 3.50/0.87    spl13_15 | ~spl13_1),
% 3.50/0.87    inference(avatar_split_clause,[],[f4214,f143,f473])).
% 3.50/0.87  fof(f143,plain,(
% 3.50/0.87    spl13_1 <=> v1_tops_1(sK8,sK7)),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 3.50/0.87  fof(f4214,plain,(
% 3.50/0.87    ( ! [X10] : (sP3(sK8,X10,sK7)) ) | ~spl13_1),
% 3.50/0.87    inference(subsumption_resolution,[],[f4213,f82])).
% 3.50/0.87  fof(f4213,plain,(
% 3.50/0.87    ( ! [X10] : (~l1_pre_topc(sK7) | sP3(sK8,X10,sK7)) ) | ~spl13_1),
% 3.50/0.87    inference(subsumption_resolution,[],[f4193,f144])).
% 3.50/0.87  fof(f144,plain,(
% 3.50/0.87    v1_tops_1(sK8,sK7) | ~spl13_1),
% 3.50/0.87    inference(avatar_component_clause,[],[f143])).
% 3.50/0.87  fof(f4193,plain,(
% 3.50/0.87    ( ! [X10] : (~v1_tops_1(sK8,sK7) | ~l1_pre_topc(sK7) | sP3(sK8,X10,sK7)) )),
% 3.50/0.87    inference(resolution,[],[f83,f3144])).
% 3.50/0.87  fof(f3144,plain,(
% 3.50/0.87    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~v1_tops_1(X1,X2) | ~l1_pre_topc(X2) | sP3(X1,X3,X2)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f3139,f887])).
% 3.50/0.87  fof(f887,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,u1_struct_0(X2))) )),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f883])).
% 3.50/0.87  fof(f883,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | r2_hidden(X1,u1_struct_0(X2)) | sP3(X0,X1,X2)) )),
% 3.50/0.87    inference(resolution,[],[f456,f125])).
% 3.50/0.87  fof(f125,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (r2_hidden(X1,sK12(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f79])).
% 3.50/0.87  fof(f456,plain,(
% 3.50/0.87    ( ! [X6,X8,X7,X9] : (~r2_hidden(X9,sK12(X6,X7,X8)) | sP3(X6,X7,X8) | r2_hidden(X9,u1_struct_0(X8))) )),
% 3.50/0.87    inference(resolution,[],[f123,f133])).
% 3.50/0.87  fof(f133,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f39])).
% 3.50/0.87  fof(f39,plain,(
% 3.50/0.87    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.50/0.87    inference(ennf_transformation,[],[f10])).
% 3.50/0.87  fof(f10,axiom,(
% 3.50/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 3.50/0.87  fof(f123,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | sP3(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f79])).
% 3.50/0.87  fof(f3139,plain,(
% 3.50/0.87    ( ! [X2,X3,X1] : (~v1_tops_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~r2_hidden(X3,u1_struct_0(X2)) | sP3(X1,X3,X2)) )),
% 3.50/0.87    inference(resolution,[],[f1902,f1007])).
% 3.50/0.87  fof(f1007,plain,(
% 3.50/0.87    ( ! [X10,X8,X7,X9] : (~sP5(X9,X10,X8) | ~r2_hidden(X7,X9) | sP3(X10,X7,X8)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f489,f887])).
% 3.50/0.87  fof(f489,plain,(
% 3.50/0.87    ( ! [X10,X8,X7,X9] : (~r2_hidden(X7,u1_struct_0(X8)) | ~sP5(X9,X10,X8) | ~r2_hidden(X7,X9) | sP3(X10,X7,X8)) )),
% 3.50/0.87    inference(resolution,[],[f115,f118])).
% 3.50/0.87  fof(f118,plain,(
% 3.50/0.87    ( ! [X2,X0,X3,X1] : (~sP4(X0,X1,X2,X3) | ~r2_hidden(X1,X3) | sP3(X2,X1,X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f75])).
% 3.50/0.87  fof(f1902,plain,(
% 3.50/0.87    ( ! [X4,X5] : (sP5(u1_struct_0(X4),X5,X4) | ~v1_tops_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f1901,f798])).
% 3.50/0.87  fof(f798,plain,(
% 3.50/0.87    ( ! [X0,X1] : (sP6(X0,X1,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(resolution,[],[f127,f170])).
% 3.50/0.87  fof(f170,plain,(
% 3.50/0.87    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(forward_demodulation,[],[f93,f89])).
% 3.50/0.87  fof(f89,plain,(
% 3.50/0.87    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.50/0.87    inference(cnf_transformation,[],[f6])).
% 3.50/0.87  fof(f6,axiom,(
% 3.50/0.87    ! [X0] : k2_subset_1(X0) = X0),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 3.50/0.87  fof(f93,plain,(
% 3.50/0.87    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(cnf_transformation,[],[f8])).
% 3.50/0.87  fof(f8,axiom,(
% 3.50/0.87    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 3.50/0.87  fof(f1901,plain,(
% 3.50/0.87    ( ! [X4,X5] : (~sP6(X4,X5,u1_struct_0(X4)) | sP5(u1_struct_0(X4),X5,X4) | ~v1_tops_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f1896,f95])).
% 3.50/0.87  fof(f95,plain,(
% 3.50/0.87    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f26])).
% 3.50/0.87  fof(f26,plain,(
% 3.50/0.87    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(ennf_transformation,[],[f15])).
% 3.50/0.87  fof(f15,axiom,(
% 3.50/0.87    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.50/0.87  fof(f1896,plain,(
% 3.50/0.87    ( ! [X4,X5] : (~sP6(X4,X5,u1_struct_0(X4)) | sP5(u1_struct_0(X4),X5,X4) | ~v1_tops_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~l1_struct_0(X4)) )),
% 3.50/0.87    inference(superposition,[],[f660,f94])).
% 3.50/0.87  fof(f94,plain,(
% 3.50/0.87    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f25])).
% 3.50/0.87  fof(f25,plain,(
% 3.50/0.87    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.50/0.87    inference(ennf_transformation,[],[f14])).
% 3.50/0.87  fof(f14,axiom,(
% 3.50/0.87    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.50/0.87  fof(f660,plain,(
% 3.50/0.87    ( ! [X12,X13] : (~sP6(X12,X13,k2_struct_0(X12)) | sP5(k2_struct_0(X12),X13,X12) | ~v1_tops_1(X13,X12) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 3.50/0.87    inference(superposition,[],[f141,f98])).
% 3.50/0.87  fof(f98,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f58])).
% 3.50/0.87  fof(f58,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(nnf_transformation,[],[f29])).
% 3.50/0.87  fof(f29,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(ennf_transformation,[],[f18])).
% 3.50/0.87  fof(f18,axiom,(
% 3.50/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 3.50/0.87  fof(f83,plain,(
% 3.50/0.87    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f2455,plain,(
% 3.50/0.87    spl13_1 | ~spl13_29 | ~spl13_36),
% 3.50/0.87    inference(avatar_contradiction_clause,[],[f2454])).
% 3.50/0.87  fof(f2454,plain,(
% 3.50/0.87    $false | (spl13_1 | ~spl13_29 | ~spl13_36)),
% 3.50/0.87    inference(subsumption_resolution,[],[f2452,f1540])).
% 3.50/0.87  fof(f1540,plain,(
% 3.50/0.87    l1_struct_0(sK7) | ~spl13_36),
% 3.50/0.87    inference(avatar_component_clause,[],[f1539])).
% 3.50/0.87  fof(f1539,plain,(
% 3.50/0.87    spl13_36 <=> l1_struct_0(sK7)),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).
% 3.50/0.87  fof(f2452,plain,(
% 3.50/0.87    ~l1_struct_0(sK7) | (spl13_1 | ~spl13_29)),
% 3.50/0.87    inference(trivial_inequality_removal,[],[f2451])).
% 3.50/0.87  fof(f2451,plain,(
% 3.50/0.87    u1_struct_0(sK7) != u1_struct_0(sK7) | ~l1_struct_0(sK7) | (spl13_1 | ~spl13_29)),
% 3.50/0.87    inference(superposition,[],[f2317,f94])).
% 3.50/0.87  fof(f2317,plain,(
% 3.50/0.87    u1_struct_0(sK7) != k2_struct_0(sK7) | (spl13_1 | ~spl13_29)),
% 3.50/0.87    inference(subsumption_resolution,[],[f2316,f82])).
% 3.50/0.87  fof(f2316,plain,(
% 3.50/0.87    u1_struct_0(sK7) != k2_struct_0(sK7) | ~l1_pre_topc(sK7) | (spl13_1 | ~spl13_29)),
% 3.50/0.87    inference(subsumption_resolution,[],[f2315,f83])).
% 3.50/0.87  fof(f2315,plain,(
% 3.50/0.87    u1_struct_0(sK7) != k2_struct_0(sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) | ~l1_pre_topc(sK7) | (spl13_1 | ~spl13_29)),
% 3.50/0.87    inference(subsumption_resolution,[],[f2312,f1457])).
% 3.50/0.87  fof(f1457,plain,(
% 3.50/0.87    sP5(u1_struct_0(sK7),sK8,sK7) | ~spl13_29),
% 3.50/0.87    inference(avatar_component_clause,[],[f1455])).
% 3.50/0.87  fof(f1455,plain,(
% 3.50/0.87    spl13_29 <=> sP5(u1_struct_0(sK7),sK8,sK7)),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).
% 3.50/0.87  fof(f2312,plain,(
% 3.50/0.87    ~sP5(u1_struct_0(sK7),sK8,sK7) | u1_struct_0(sK7) != k2_struct_0(sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) | ~l1_pre_topc(sK7) | spl13_1),
% 3.50/0.87    inference(resolution,[],[f2309,f798])).
% 3.50/0.87  fof(f2309,plain,(
% 3.50/0.87    ( ! [X4] : (~sP6(sK7,sK8,X4) | ~sP5(X4,sK8,sK7) | k2_struct_0(sK7) != X4) ) | spl13_1),
% 3.50/0.87    inference(subsumption_resolution,[],[f2308,f82])).
% 3.50/0.87  fof(f2308,plain,(
% 3.50/0.87    ( ! [X4] : (k2_struct_0(sK7) != X4 | ~l1_pre_topc(sK7) | ~sP5(X4,sK8,sK7) | ~sP6(sK7,sK8,X4)) ) | spl13_1),
% 3.50/0.87    inference(subsumption_resolution,[],[f2303,f145])).
% 3.50/0.87  fof(f145,plain,(
% 3.50/0.87    ~v1_tops_1(sK8,sK7) | spl13_1),
% 3.50/0.87    inference(avatar_component_clause,[],[f143])).
% 3.50/0.87  fof(f2303,plain,(
% 3.50/0.87    ( ! [X4] : (v1_tops_1(sK8,sK7) | k2_struct_0(sK7) != X4 | ~l1_pre_topc(sK7) | ~sP5(X4,sK8,sK7) | ~sP6(sK7,sK8,X4)) )),
% 3.50/0.87    inference(resolution,[],[f682,f83])).
% 3.50/0.87  fof(f682,plain,(
% 3.50/0.87    ( ! [X4,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v1_tops_1(X3,X2) | k2_struct_0(X2) != X4 | ~l1_pre_topc(X2) | ~sP5(X4,X3,X2) | ~sP6(X2,X3,X4)) )),
% 3.50/0.87    inference(superposition,[],[f99,f114])).
% 3.50/0.87  fof(f99,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f58])).
% 3.50/0.87  fof(f2133,plain,(
% 3.50/0.87    ~spl13_21 | ~spl13_63),
% 3.50/0.87    inference(avatar_contradiction_clause,[],[f2132])).
% 3.50/0.87  fof(f2132,plain,(
% 3.50/0.87    $false | (~spl13_21 | ~spl13_63)),
% 3.50/0.87    inference(subsumption_resolution,[],[f2131,f82])).
% 3.50/0.87  fof(f2131,plain,(
% 3.50/0.87    ~l1_pre_topc(sK7) | (~spl13_21 | ~spl13_63)),
% 3.50/0.87    inference(resolution,[],[f2090,f718])).
% 3.50/0.87  fof(f2090,plain,(
% 3.50/0.87    ( ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) ) | ~spl13_63),
% 3.50/0.87    inference(avatar_component_clause,[],[f2089])).
% 3.50/0.87  fof(f2089,plain,(
% 3.50/0.87    spl13_63 <=> ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0))),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).
% 3.50/0.87  fof(f2128,plain,(
% 3.50/0.87    spl13_63 | ~spl13_65),
% 3.50/0.87    inference(avatar_split_clause,[],[f2124,f2111,f2089])).
% 3.50/0.87  fof(f2111,plain,(
% 3.50/0.87    spl13_65 <=> ! [X4] : (~l1_pre_topc(X4) | ~v3_pre_topc(u1_struct_0(X4),X4))),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).
% 3.50/0.87  fof(f2124,plain,(
% 3.50/0.87    ( ! [X3] : (~v4_pre_topc(k1_xboole_0,X3) | ~l1_pre_topc(X3)) ) | ~spl13_65),
% 3.50/0.87    inference(subsumption_resolution,[],[f762,f2112])).
% 3.50/0.87  fof(f2112,plain,(
% 3.50/0.87    ( ! [X4] : (~v3_pre_topc(u1_struct_0(X4),X4) | ~l1_pre_topc(X4)) ) | ~spl13_65),
% 3.50/0.87    inference(avatar_component_clause,[],[f2111])).
% 3.50/0.87  fof(f762,plain,(
% 3.50/0.87    ( ! [X3] : (v3_pre_topc(u1_struct_0(X3),X3) | ~v4_pre_topc(k1_xboole_0,X3) | ~l1_pre_topc(X3)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f756,f90])).
% 3.50/0.87  fof(f756,plain,(
% 3.50/0.87    ( ! [X3] : (v3_pre_topc(u1_struct_0(X3),X3) | ~v4_pre_topc(k1_xboole_0,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 3.50/0.87    inference(superposition,[],[f100,f373])).
% 3.50/0.87  fof(f373,plain,(
% 3.50/0.87    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f363,f170])).
% 3.50/0.87  fof(f363,plain,(
% 3.50/0.87    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.50/0.87    inference(superposition,[],[f234,f200])).
% 3.50/0.87  fof(f200,plain,(
% 3.50/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.50/0.87    inference(forward_demodulation,[],[f137,f92])).
% 3.50/0.87  fof(f92,plain,(
% 3.50/0.87    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.50/0.87    inference(cnf_transformation,[],[f4])).
% 3.50/0.87  fof(f4,axiom,(
% 3.50/0.87    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.50/0.87  fof(f137,plain,(
% 3.50/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.50/0.87    inference(definition_unfolding,[],[f91,f130])).
% 3.50/0.87  fof(f130,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.50/0.87    inference(cnf_transformation,[],[f5])).
% 3.50/0.87  fof(f5,axiom,(
% 3.50/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.50/0.87  fof(f91,plain,(
% 3.50/0.87    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f3])).
% 3.50/0.87  fof(f3,axiom,(
% 3.50/0.87    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 3.50/0.87  fof(f234,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f231])).
% 3.50/0.87  fof(f231,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(superposition,[],[f132,f131])).
% 3.50/0.87  fof(f131,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(cnf_transformation,[],[f37])).
% 3.50/0.87  fof(f37,plain,(
% 3.50/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.50/0.87    inference(ennf_transformation,[],[f7])).
% 3.50/0.87  fof(f7,axiom,(
% 3.50/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.50/0.87  fof(f132,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.50/0.87    inference(cnf_transformation,[],[f38])).
% 3.50/0.87  fof(f38,plain,(
% 3.50/0.87    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.50/0.87    inference(ennf_transformation,[],[f9])).
% 3.50/0.87  fof(f9,axiom,(
% 3.50/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.50/0.87  fof(f100,plain,(
% 3.50/0.87    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f59])).
% 3.50/0.87  fof(f59,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(nnf_transformation,[],[f30])).
% 3.50/0.87  fof(f30,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(ennf_transformation,[],[f20])).
% 3.50/0.87  fof(f20,axiom,(
% 3.50/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 3.50/0.87  fof(f2113,plain,(
% 3.50/0.87    spl13_65 | spl13_19),
% 3.50/0.87    inference(avatar_split_clause,[],[f2109,f642,f2111])).
% 3.50/0.87  fof(f2109,plain,(
% 3.50/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~l1_pre_topc(X4) | ~v3_pre_topc(u1_struct_0(X4),X4)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f2108,f206])).
% 3.50/0.87  fof(f206,plain,(
% 3.50/0.87    ( ! [X2,X1] : (r2_hidden(X1,X2) | ~r2_hidden(X1,k1_xboole_0)) )),
% 3.50/0.87    inference(resolution,[],[f133,f90])).
% 3.50/0.87  fof(f2108,plain,(
% 3.50/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~l1_pre_topc(X4) | ~v3_pre_topc(u1_struct_0(X4),X4) | ~r2_hidden(X3,u1_struct_0(X4))) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f2101,f262])).
% 3.50/0.87  fof(f262,plain,(
% 3.50/0.87    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 3.50/0.87    inference(trivial_inequality_removal,[],[f259])).
% 3.50/0.87  fof(f259,plain,(
% 3.50/0.87    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X3)) )),
% 3.50/0.87    inference(superposition,[],[f139,f247])).
% 3.50/0.87  fof(f247,plain,(
% 3.50/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 3.50/0.87    inference(forward_demodulation,[],[f235,f200])).
% 3.50/0.87  fof(f235,plain,(
% 3.50/0.87    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 3.50/0.87    inference(superposition,[],[f138,f92])).
% 3.50/0.87  fof(f138,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.50/0.87    inference(definition_unfolding,[],[f129,f130,f130])).
% 3.50/0.87  fof(f129,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f1])).
% 3.50/0.87  fof(f1,axiom,(
% 3.50/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.50/0.87  fof(f139,plain,(
% 3.50/0.87    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.50/0.87    inference(definition_unfolding,[],[f135,f130])).
% 3.50/0.87  fof(f135,plain,(
% 3.50/0.87    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.50/0.87    inference(cnf_transformation,[],[f80])).
% 3.50/0.87  fof(f80,plain,(
% 3.50/0.87    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.50/0.87    inference(nnf_transformation,[],[f2])).
% 3.50/0.87  fof(f2,axiom,(
% 3.50/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.50/0.87  fof(f2101,plain,(
% 3.50/0.87    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~l1_pre_topc(X4) | ~v3_pre_topc(u1_struct_0(X4),X4) | ~r1_xboole_0(k1_xboole_0,u1_struct_0(X4)) | ~r2_hidden(X3,u1_struct_0(X4))) )),
% 3.50/0.87    inference(resolution,[],[f647,f849])).
% 3.50/0.87  fof(f849,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~sP0(X2,X0,X1) | ~v3_pre_topc(u1_struct_0(X1),X1) | ~r1_xboole_0(X2,u1_struct_0(X1)) | ~r2_hidden(X0,u1_struct_0(X1))) )),
% 3.50/0.87    inference(resolution,[],[f107,f170])).
% 3.50/0.87  fof(f647,plain,(
% 3.50/0.87    ( ! [X0,X1] : (sP0(k1_xboole_0,X1,X0) | ~r2_hidden(X1,k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(resolution,[],[f646,f105])).
% 3.50/0.87  fof(f105,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f64])).
% 3.50/0.87  fof(f64,plain,(
% 3.50/0.87    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | v2_struct_0(X0)) & ((sP0(X2,X1,X0) & ~v2_struct_0(X0)) | ~sP1(X0,X1,X2)))),
% 3.50/0.87    inference(rectify,[],[f63])).
% 3.50/0.87  fof(f63,plain,(
% 3.50/0.87    ! [X0,X2,X1] : ((sP1(X0,X2,X1) | ~sP0(X1,X2,X0) | v2_struct_0(X0)) & ((sP0(X1,X2,X0) & ~v2_struct_0(X0)) | ~sP1(X0,X2,X1)))),
% 3.50/0.87    inference(flattening,[],[f62])).
% 3.50/0.87  fof(f62,plain,(
% 3.50/0.87    ! [X0,X2,X1] : ((sP1(X0,X2,X1) | (~sP0(X1,X2,X0) | v2_struct_0(X0))) & ((sP0(X1,X2,X0) & ~v2_struct_0(X0)) | ~sP1(X0,X2,X1)))),
% 3.50/0.87    inference(nnf_transformation,[],[f43])).
% 3.50/0.87  fof(f43,plain,(
% 3.50/0.87    ! [X0,X2,X1] : (sP1(X0,X2,X1) <=> (sP0(X1,X2,X0) & ~v2_struct_0(X0)))),
% 3.50/0.87    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.50/0.87  fof(f646,plain,(
% 3.50/0.87    ( ! [X0,X1] : (sP1(X1,X0,k1_xboole_0) | ~l1_pre_topc(X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f645,f209])).
% 3.50/0.87  fof(f209,plain,(
% 3.50/0.87    ( ! [X2,X1] : (~r2_hidden(X1,k1_xboole_0) | m1_subset_1(X1,X2)) )),
% 3.50/0.87    inference(resolution,[],[f136,f90])).
% 3.50/0.87  fof(f136,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f41])).
% 3.50/0.87  fof(f41,plain,(
% 3.50/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.50/0.87    inference(flattening,[],[f40])).
% 3.50/0.87  fof(f40,plain,(
% 3.50/0.87    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.50/0.87    inference(ennf_transformation,[],[f12])).
% 3.50/0.87  fof(f12,axiom,(
% 3.50/0.87    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 3.50/0.87  fof(f645,plain,(
% 3.50/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X1) | sP1(X1,X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 3.50/0.87    inference(resolution,[],[f628,f478])).
% 3.50/0.87  fof(f478,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~sP2(X2,X1,X0) | sP1(X0,X1,X2) | ~r2_hidden(X1,k1_xboole_0)) )),
% 3.50/0.87    inference(resolution,[],[f102,f206])).
% 3.50/0.87  fof(f102,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(X2,X0)) | sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f61])).
% 3.50/0.87  fof(f61,plain,(
% 3.50/0.87    ! [X0,X1,X2] : (((r2_hidden(X1,k2_pre_topc(X2,X0)) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_hidden(X1,k2_pre_topc(X2,X0)))) | ~sP2(X0,X1,X2))),
% 3.50/0.87    inference(rectify,[],[f60])).
% 3.50/0.87  fof(f60,plain,(
% 3.50/0.87    ! [X1,X2,X0] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ~sP1(X0,X2,X1)) & (sP1(X0,X2,X1) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~sP2(X1,X2,X0))),
% 3.50/0.87    inference(nnf_transformation,[],[f44])).
% 3.50/0.87  fof(f44,plain,(
% 3.50/0.87    ! [X1,X2,X0] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> sP1(X0,X2,X1)) | ~sP2(X1,X2,X0))),
% 3.50/0.87    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.50/0.87  fof(f628,plain,(
% 3.50/0.87    ( ! [X2,X3] : (sP2(k1_xboole_0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X3)) | ~l1_pre_topc(X3)) )),
% 3.50/0.87    inference(resolution,[],[f112,f90])).
% 3.50/0.87  fof(f112,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | sP2(X1,X2,X0) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f45])).
% 3.50/0.87  fof(f45,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : (! [X2] : (sP2(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(definition_folding,[],[f32,f44,f43,f42])).
% 3.50/0.87  fof(f32,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(flattening,[],[f31])).
% 3.50/0.87  fof(f31,plain,(
% 3.50/0.87    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & ~v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.50/0.87    inference(ennf_transformation,[],[f17])).
% 3.50/0.87  fof(f17,axiom,(
% 3.50/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0))) & ~v2_struct_0(X0))))))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).
% 3.50/0.87  fof(f1963,plain,(
% 3.50/0.87    spl13_15 | ~spl13_6 | ~spl13_19),
% 3.50/0.87    inference(avatar_split_clause,[],[f671,f642,f167,f473])).
% 3.50/0.87  fof(f167,plain,(
% 3.50/0.87    spl13_6 <=> ! [X3] : (~r1_xboole_0(sK8,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) | k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK7))),
% 3.50/0.87    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 3.50/0.87  fof(f671,plain,(
% 3.50/0.87    ( ! [X4] : (sP3(sK8,X4,sK7)) ) | (~spl13_6 | ~spl13_19)),
% 3.50/0.87    inference(subsumption_resolution,[],[f468,f643])).
% 3.50/0.87  fof(f468,plain,(
% 3.50/0.87    ( ! [X4] : (sP3(sK8,X4,sK7) | r2_hidden(X4,k1_xboole_0)) ) | ~spl13_6),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f465])).
% 3.50/0.87  fof(f465,plain,(
% 3.50/0.87    ( ! [X4] : (r2_hidden(X4,k1_xboole_0) | sP3(sK8,X4,sK7) | sP3(sK8,X4,sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(superposition,[],[f125,f460])).
% 3.50/0.87  fof(f460,plain,(
% 3.50/0.87    ( ! [X0] : (k1_xboole_0 = sK12(sK8,X0,sK7) | sP3(sK8,X0,sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f458])).
% 3.50/0.87  fof(f458,plain,(
% 3.50/0.87    ( ! [X0] : (sP3(sK8,X0,sK7) | k1_xboole_0 = sK12(sK8,X0,sK7) | sP3(sK8,X0,sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(resolution,[],[f457,f126])).
% 3.50/0.87  fof(f126,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (r1_xboole_0(X0,sK12(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f79])).
% 3.50/0.87  fof(f457,plain,(
% 3.50/0.87    ( ! [X0,X1] : (~r1_xboole_0(sK8,sK12(X0,X1,sK7)) | sP3(X0,X1,sK7) | k1_xboole_0 = sK12(X0,X1,sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(subsumption_resolution,[],[f454,f124])).
% 3.50/0.87  fof(f124,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (v3_pre_topc(sK12(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f79])).
% 3.50/0.87  fof(f454,plain,(
% 3.50/0.87    ( ! [X0,X1] : (sP3(X0,X1,sK7) | ~r1_xboole_0(sK8,sK12(X0,X1,sK7)) | k1_xboole_0 = sK12(X0,X1,sK7) | ~v3_pre_topc(sK12(X0,X1,sK7),sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(resolution,[],[f123,f168])).
% 3.50/0.87  fof(f168,plain,(
% 3.50/0.87    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) | ~r1_xboole_0(sK8,X3) | k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK7)) ) | ~spl13_6),
% 3.50/0.87    inference(avatar_component_clause,[],[f167])).
% 3.50/0.87  fof(f1549,plain,(
% 3.50/0.87    spl13_36),
% 3.50/0.87    inference(avatar_contradiction_clause,[],[f1548])).
% 3.50/0.87  fof(f1548,plain,(
% 3.50/0.87    $false | spl13_36),
% 3.50/0.87    inference(subsumption_resolution,[],[f1547,f82])).
% 3.50/0.87  fof(f1547,plain,(
% 3.50/0.87    ~l1_pre_topc(sK7) | spl13_36),
% 3.50/0.87    inference(resolution,[],[f1541,f95])).
% 3.50/0.87  fof(f1541,plain,(
% 3.50/0.87    ~l1_struct_0(sK7) | spl13_36),
% 3.50/0.87    inference(avatar_component_clause,[],[f1539])).
% 3.50/0.87  fof(f1459,plain,(
% 3.50/0.87    spl13_29 | ~spl13_15),
% 3.50/0.87    inference(avatar_split_clause,[],[f1449,f473,f1455])).
% 3.50/0.87  fof(f1449,plain,(
% 3.50/0.87    sP5(u1_struct_0(sK7),sK8,sK7) | ~spl13_15),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f1445])).
% 3.50/0.87  fof(f1445,plain,(
% 3.50/0.87    sP5(u1_struct_0(sK7),sK8,sK7) | sP5(u1_struct_0(sK7),sK8,sK7) | ~spl13_15),
% 3.50/0.87    inference(resolution,[],[f1437,f116])).
% 3.50/0.87  fof(f1437,plain,(
% 3.50/0.87    ( ! [X0] : (~r2_hidden(sK11(X0,sK8,sK7),X0) | sP5(X0,sK8,sK7)) ) | ~spl13_15),
% 3.50/0.87    inference(resolution,[],[f449,f474])).
% 3.50/0.87  fof(f449,plain,(
% 3.50/0.87    ( ! [X2,X0,X1] : (~sP3(X0,sK11(X1,X0,X2),X2) | ~r2_hidden(sK11(X1,X0,X2),X1) | sP5(X1,X0,X2)) )),
% 3.50/0.87    inference(resolution,[],[f121,f117])).
% 3.50/0.87  fof(f121,plain,(
% 3.50/0.87    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | ~sP3(X2,X1,X0) | ~r2_hidden(X1,X3)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f75])).
% 3.50/0.87  fof(f792,plain,(
% 3.50/0.87    spl13_21),
% 3.50/0.87    inference(avatar_contradiction_clause,[],[f791])).
% 3.50/0.87  fof(f791,plain,(
% 3.50/0.87    $false | spl13_21),
% 3.50/0.87    inference(subsumption_resolution,[],[f790,f81])).
% 3.50/0.87  fof(f81,plain,(
% 3.50/0.87    v2_pre_topc(sK7)),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f790,plain,(
% 3.50/0.87    ~v2_pre_topc(sK7) | spl13_21),
% 3.50/0.87    inference(subsumption_resolution,[],[f789,f82])).
% 3.50/0.87  fof(f789,plain,(
% 3.50/0.87    ~l1_pre_topc(sK7) | ~v2_pre_topc(sK7) | spl13_21),
% 3.50/0.87    inference(resolution,[],[f787,f719])).
% 3.50/0.87  fof(f719,plain,(
% 3.50/0.87    ~v4_pre_topc(k1_xboole_0,sK7) | spl13_21),
% 3.50/0.87    inference(avatar_component_clause,[],[f717])).
% 3.50/0.87  fof(f787,plain,(
% 3.50/0.87    ( ! [X1] : (v4_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 3.50/0.87    inference(duplicate_literal_removal,[],[f784])).
% 3.50/0.87  fof(f784,plain,(
% 3.50/0.87    ( ! [X1] : (v4_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 3.50/0.87    inference(resolution,[],[f778,f202])).
% 3.50/0.87  fof(f202,plain,(
% 3.50/0.87    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f201,f95])).
% 3.50/0.87  fof(f201,plain,(
% 3.50/0.87    ( ! [X0] : (v3_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~l1_struct_0(X0)) )),
% 3.50/0.87    inference(superposition,[],[f128,f94])).
% 3.50/0.87  fof(f128,plain,(
% 3.50/0.87    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f36])).
% 3.50/0.87  fof(f36,plain,(
% 3.50/0.87    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.50/0.87    inference(flattening,[],[f35])).
% 3.50/0.87  fof(f35,plain,(
% 3.50/0.87    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.50/0.87    inference(ennf_transformation,[],[f19])).
% 3.50/0.87  fof(f19,axiom,(
% 3.50/0.87    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.50/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 3.50/0.87  fof(f778,plain,(
% 3.50/0.87    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),X3) | v4_pre_topc(k1_xboole_0,X3) | ~l1_pre_topc(X3)) )),
% 3.50/0.87    inference(subsumption_resolution,[],[f771,f90])).
% 3.50/0.87  fof(f771,plain,(
% 3.50/0.87    ( ! [X3] : (~v3_pre_topc(u1_struct_0(X3),X3) | v4_pre_topc(k1_xboole_0,X3) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 3.50/0.87    inference(superposition,[],[f101,f373])).
% 3.50/0.87  fof(f101,plain,(
% 3.50/0.87    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f59])).
% 3.50/0.87  fof(f169,plain,(
% 3.50/0.87    spl13_1 | spl13_6),
% 3.50/0.87    inference(avatar_split_clause,[],[f84,f167,f143])).
% 3.50/0.87  fof(f84,plain,(
% 3.50/0.87    ( ! [X3] : (~r1_xboole_0(sK8,X3) | ~v3_pre_topc(X3,sK7) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) | v1_tops_1(sK8,sK7)) )),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f165,plain,(
% 3.50/0.87    ~spl13_1 | spl13_5),
% 3.50/0.87    inference(avatar_split_clause,[],[f85,f162,f143])).
% 3.50/0.87  fof(f85,plain,(
% 3.50/0.87    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) | ~v1_tops_1(sK8,sK7)),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f160,plain,(
% 3.50/0.87    ~spl13_1 | ~spl13_4),
% 3.50/0.87    inference(avatar_split_clause,[],[f86,f157,f143])).
% 3.50/0.87  fof(f86,plain,(
% 3.50/0.87    k1_xboole_0 != sK9 | ~v1_tops_1(sK8,sK7)),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f155,plain,(
% 3.50/0.87    ~spl13_1 | spl13_3),
% 3.50/0.87    inference(avatar_split_clause,[],[f87,f152,f143])).
% 3.50/0.87  fof(f87,plain,(
% 3.50/0.87    v3_pre_topc(sK9,sK7) | ~v1_tops_1(sK8,sK7)),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  fof(f150,plain,(
% 3.50/0.87    ~spl13_1 | spl13_2),
% 3.50/0.87    inference(avatar_split_clause,[],[f88,f147,f143])).
% 3.50/0.87  fof(f88,plain,(
% 3.50/0.87    r1_xboole_0(sK8,sK9) | ~v1_tops_1(sK8,sK7)),
% 3.50/0.87    inference(cnf_transformation,[],[f57])).
% 3.50/0.87  % SZS output end Proof for theBenchmark
% 3.50/0.87  % (23769)------------------------------
% 3.50/0.87  % (23769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.87  % (23769)Termination reason: Refutation
% 3.50/0.87  
% 3.50/0.87  % (23769)Memory used [KB]: 8059
% 3.50/0.87  % (23769)Time elapsed: 0.429 s
% 3.50/0.87  % (23769)------------------------------
% 3.50/0.87  % (23769)------------------------------
% 3.50/0.87  % (23741)Success in time 0.506 s
%------------------------------------------------------------------------------
