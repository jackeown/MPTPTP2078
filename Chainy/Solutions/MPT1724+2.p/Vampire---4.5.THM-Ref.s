%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1724+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 760 expanded)
%              Number of leaves         :   16 ( 330 expanded)
%              Depth                    :   47
%              Number of atoms          :  731 (10269 expanded)
%              Number of equality atoms :   89 (1698 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8939,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8938,f6203])).

fof(f6203,plain,(
    l1_pre_topc(sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f5066,plain,
    ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK266,sK264))
      | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266)) )
    & ( r1_tsep_1(sK266,sK265)
      | r1_tsep_1(sK265,sK266) )
    & m1_pre_topc(sK264,sK265)
    & m1_pre_topc(sK266,sK263)
    & ~ v2_struct_0(sK266)
    & m1_pre_topc(sK265,sK263)
    & ~ v2_struct_0(sK265)
    & m1_pre_topc(sK264,sK263)
    & ~ v2_struct_0(sK264)
    & l1_pre_topc(sK263)
    & v2_pre_topc(sK263)
    & ~ v2_struct_0(sK263) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK263,sK264,sK265,sK266])],[f3401,f5065,f5064,f5063,f5062])).

fof(f5062,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
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
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X3,X1))
                    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X1,X3)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK263)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK263)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK263)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK263)
      & v2_pre_topc(sK263)
      & ~ v2_struct_0(sK263) ) ),
    introduced(choice_axiom,[])).

fof(f5063,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X3,X1))
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X1,X3)) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK263)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK263)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK263)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X3,sK264))
                | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,sK264,X3)) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK264,X2)
              & m1_pre_topc(X3,sK263)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK263)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK264,sK263)
      & ~ v2_struct_0(sK264) ) ),
    introduced(choice_axiom,[])).

fof(f5064,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,X3,sK264))
              | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,X2,k1_tsep_1(sK263,sK264,X3)) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK264,X2)
            & m1_pre_topc(X3,sK263)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK263)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,X3,sK264))
            | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,X3)) )
          & ( r1_tsep_1(X3,sK265)
            | r1_tsep_1(sK265,X3) )
          & m1_pre_topc(sK264,sK265)
          & m1_pre_topc(X3,sK263)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK265,sK263)
      & ~ v2_struct_0(sK265) ) ),
    introduced(choice_axiom,[])).

fof(f5065,plain,
    ( ? [X3] :
        ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,X3,sK264))
          | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,X3)) )
        & ( r1_tsep_1(X3,sK265)
          | r1_tsep_1(sK265,X3) )
        & m1_pre_topc(sK264,sK265)
        & m1_pre_topc(X3,sK263)
        & ~ v2_struct_0(X3) )
   => ( ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK266,sK264))
        | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266)) )
      & ( r1_tsep_1(sK266,sK265)
        | r1_tsep_1(sK265,sK266) )
      & m1_pre_topc(sK264,sK265)
      & m1_pre_topc(sK266,sK263)
      & ~ v2_struct_0(sK266) ) ),
    introduced(choice_axiom,[])).

fof(f3401,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3400])).

fof(f3400,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3372])).

fof(f3372,negated_conjecture,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3371])).

fof(f3371,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f8938,plain,(
    ~ l1_pre_topc(sK263) ),
    inference(subsumption_resolution,[],[f8937,f6205])).

fof(f6205,plain,(
    m1_pre_topc(sK264,sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8937,plain,
    ( ~ m1_pre_topc(sK264,sK263)
    | ~ l1_pre_topc(sK263) ),
    inference(subsumption_resolution,[],[f8936,f6202])).

fof(f6202,plain,(
    v2_pre_topc(sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8936,plain,
    ( ~ v2_pre_topc(sK263)
    | ~ m1_pre_topc(sK264,sK263)
    | ~ l1_pre_topc(sK263) ),
    inference(subsumption_resolution,[],[f8931,f6201])).

fof(f6201,plain,(
    ~ v2_struct_0(sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8931,plain,
    ( v2_struct_0(sK263)
    | ~ v2_pre_topc(sK263)
    | ~ m1_pre_topc(sK264,sK263)
    | ~ l1_pre_topc(sK263) ),
    inference(resolution,[],[f8930,f6207])).

fof(f6207,plain,(
    m1_pre_topc(sK265,sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8930,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK265,X1)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ m1_pre_topc(sK264,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(global_subsumption,[],[f6211,f8921,f8929])).

fof(f8929,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK265,sK266)
      | ~ m1_pre_topc(sK265,X1)
      | ~ m1_pre_topc(sK264,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8928,f6204])).

fof(f6204,plain,(
    ~ v2_struct_0(sK264) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8928,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK265,sK266)
      | ~ m1_pre_topc(sK265,X1)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8927,f6206])).

fof(f6206,plain,(
    ~ v2_struct_0(sK265) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8927,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK265,sK266)
      | ~ m1_pre_topc(sK265,X1)
      | v2_struct_0(sK265)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8923,f6210])).

fof(f6210,plain,(
    m1_pre_topc(sK264,sK265) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8923,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK265,sK266)
      | ~ m1_pre_topc(sK264,sK265)
      | ~ m1_pre_topc(sK265,X1)
      | v2_struct_0(sK265)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f8910,f6409])).

fof(f6409,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3501])).

fof(f3501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3500])).

fof(f3500,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3356])).

fof(f3356,axiom,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f8910,plain,
    ( r1_tsep_1(sK265,sK264)
    | ~ r1_tsep_1(sK265,sK266) ),
    inference(resolution,[],[f8908,f6226])).

fof(f6226,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f5074])).

fof(f5074,plain,(
    ! [X0,X1] :
      ( ( ~ r1_tsep_1(X1,X0)
        & ~ r1_tsep_1(X0,X1) )
      | ~ sP4(X0,X1) ) ),
    inference(rectify,[],[f5073])).

fof(f5073,plain,(
    ! [X3,X2] :
      ( ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ~ sP4(X3,X2) ) ),
    inference(nnf_transformation,[],[f4655])).

fof(f4655,plain,(
    ! [X3,X2] :
      ( ( ~ r1_tsep_1(X2,X3)
        & ~ r1_tsep_1(X3,X2) )
      | ~ sP4(X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f8908,plain,
    ( sP4(sK266,sK265)
    | r1_tsep_1(sK265,sK264) ),
    inference(subsumption_resolution,[],[f8907,f6228])).

fof(f6228,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f5076])).

fof(f5076,plain,(
    ! [X0,X1] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X0,X1) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f5075])).

fof(f5075,plain,(
    ! [X1,X2] :
      ( ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP3(X1,X2) ) ),
    inference(nnf_transformation,[],[f4654])).

fof(f4654,plain,(
    ! [X1,X2] :
      ( ( r1_tsep_1(X2,X1)
        & r1_tsep_1(X1,X2) )
      | ~ sP3(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f8907,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264) ),
    inference(subsumption_resolution,[],[f8906,f6201])).

fof(f8906,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8905,f6202])).

fof(f8905,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8904,f6203])).

fof(f8904,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8903,f6206])).

fof(f8903,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | v2_struct_0(sK265)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8902,f6207])).

fof(f8902,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8901,f6204])).

fof(f8901,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | v2_struct_0(sK264)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8900,f6205])).

fof(f8900,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | r1_tsep_1(sK265,sK264)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(resolution,[],[f8899,f6245])).

fof(f6245,plain,(
    ! [X2,X0,X1] :
      ( sP9(X1,X2,X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4663])).

fof(f4663,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP9(X1,X2,X0)
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f3415,f4662])).

fof(f4662,plain,(
    ! [X1,X2,X0] :
      ( ( ( m1_pre_topc(X2,X1)
          | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X2,X1) )
        & ( m1_pre_topc(X1,X2)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X1,X2) ) )
      | ~ sP9(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f3415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3414])).

fof(f3414,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3369])).

fof(f3369,axiom,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2) )
                  & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tsep_1)).

fof(f8899,plain,
    ( ~ sP9(sK265,sK264,sK263)
    | sP4(sK266,sK265)
    | sP3(sK264,sK265) ),
    inference(subsumption_resolution,[],[f8898,f6201])).

fof(f8898,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8897,f6202])).

fof(f8897,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8896,f6203])).

fof(f8896,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8895,f6204])).

fof(f8895,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8894,f6205])).

fof(f8894,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8893,f6206])).

fof(f8893,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | v2_struct_0(sK265)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8892,f6207])).

fof(f8892,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8891,f6208])).

fof(f6208,plain,(
    ~ v2_struct_0(sK266) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8891,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | v2_struct_0(sK266)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8890,f6209])).

fof(f6209,plain,(
    m1_pre_topc(sK266,sK263) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8890,plain,
    ( sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263)
    | ~ m1_pre_topc(sK266,sK263)
    | v2_struct_0(sK266)
    | ~ m1_pre_topc(sK265,sK263)
    | v2_struct_0(sK265)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | ~ v2_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(resolution,[],[f8889,f6234])).

fof(f6234,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X1,X2,X0,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4658])).

fof(f4658,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( sP6(X1,X2,X0,X3)
                    & sP5(X3,X2,X0,X1) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f3411,f4657,f4656,f4655,f4654,f4653,f4652])).

fof(f4652,plain,(
    ! [X1,X2] :
      ( ( ~ r1_tsep_1(X2,X1)
        & ~ r1_tsep_1(X1,X2) )
      | ~ sP1(X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4653,plain,(
    ! [X3,X2] :
      ( ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X3,X2) )
      | ~ sP2(X3,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f4656,plain,(
    ! [X3,X2,X0,X1] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
      | sP2(X3,X2)
      | sP1(X1,X2)
      | ~ sP5(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f4657,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | sP4(X3,X2)
      | sP3(X1,X2)
      | ~ sP6(X1,X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f3411,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3410])).

fof(f3410,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                      | ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X3,X2) )
                      | ( r1_tsep_1(X2,X1)
                        & r1_tsep_1(X1,X2) ) )
                    & ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                        & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X3,X2) )
                      | ( ~ r1_tsep_1(X2,X1)
                        & ~ r1_tsep_1(X1,X2) ) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3368])).

fof(f3368,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( ~ ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
                            & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X3,X2) )
                        & ~ ( r1_tsep_1(X2,X1)
                            & r1_tsep_1(X1,X2) ) )
                    & ~ ( ~ ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X3)
                            & k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) = k2_tsep_1(X0,X3,X2) )
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X3,X2) )
                        & ( r1_tsep_1(X2,X1)
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tmap_1)).

fof(f8889,plain,
    ( ~ sP6(sK264,sK265,sK263,sK266)
    | sP3(sK264,sK265)
    | sP4(sK266,sK265)
    | ~ sP9(sK265,sK264,sK263) ),
    inference(subsumption_resolution,[],[f8886,f6210])).

fof(f8886,plain,
    ( sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | ~ sP6(sK264,sK265,sK263,sK266)
    | ~ m1_pre_topc(sK264,sK265)
    | ~ sP9(sK265,sK264,sK263) ),
    inference(equality_resolution,[],[f8831])).

fof(f8831,plain,(
    ! [X2,X3] :
      ( k2_tsep_1(sK263,sK265,sK264) != k2_tsep_1(X2,X3,sK264)
      | sP4(sK266,sK265)
      | sP3(sK264,sK265)
      | ~ sP6(sK264,sK265,sK263,sK266)
      | ~ m1_pre_topc(sK264,X3)
      | ~ sP9(X3,sK264,X2) ) ),
    inference(superposition,[],[f8816,f6243])).

fof(f6243,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X2,X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f5090])).

fof(f5090,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_pre_topc(X1,X0)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X2,X0,X1) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X2,X0,X1)
          | ~ m1_pre_topc(X1,X0) )
        & ( m1_pre_topc(X0,X1)
          | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k2_tsep_1(X2,X0,X1) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k2_tsep_1(X2,X0,X1)
          | ~ m1_pre_topc(X0,X1) ) )
      | ~ sP9(X0,X1,X2) ) ),
    inference(rectify,[],[f5089])).

fof(f5089,plain,(
    ! [X1,X2,X0] :
      ( ( ( m1_pre_topc(X2,X1)
          | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X2,X1) )
        & ( m1_pre_topc(X1,X2)
          | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k2_tsep_1(X0,X1,X2) )
        & ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X2)
          | ~ m1_pre_topc(X1,X2) ) )
      | ~ sP9(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f4662])).

fof(f8816,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,sK264)
    | sP4(sK266,sK265)
    | sP3(sK264,sK265)
    | ~ sP6(sK264,sK265,sK263,sK266) ),
    inference(superposition,[],[f8805,f6222])).

fof(f6222,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0)
      | sP4(X3,X1)
      | sP3(X0,X1)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f5070])).

fof(f5070,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_tsep_1(X2,X1,k1_tsep_1(X2,X0,X3)) = k2_tsep_1(X2,X1,X0)
        & k2_tsep_1(X2,X0,X1) = k2_tsep_1(X2,k1_tsep_1(X2,X0,X3),X1) )
      | sP4(X3,X1)
      | sP3(X0,X1)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f5069])).

fof(f5069,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) = k2_tsep_1(X0,X2,X1)
        & k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,k1_tsep_1(X0,X1,X3),X2) )
      | sP4(X3,X2)
      | sP3(X1,X2)
      | ~ sP6(X1,X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f4657])).

fof(f8805,plain,(
    g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266)) ),
    inference(subsumption_resolution,[],[f8804,f6201])).

fof(f8804,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8803,f6203])).

fof(f8803,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8802,f6204])).

fof(f8802,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8801,f6205])).

fof(f8801,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8800,f6208])).

fof(f8800,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | v2_struct_0(sK266)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(subsumption_resolution,[],[f8799,f6209])).

fof(f8799,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | ~ m1_pre_topc(sK266,sK263)
    | v2_struct_0(sK266)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(duplicate_literal_removal,[],[f8793])).

fof(f8793,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266))
    | ~ m1_pre_topc(sK266,sK263)
    | v2_struct_0(sK266)
    | ~ m1_pre_topc(sK264,sK263)
    | v2_struct_0(sK264)
    | ~ l1_pre_topc(sK263)
    | v2_struct_0(sK263) ),
    inference(superposition,[],[f6212,f6257])).

fof(f6257,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3425])).

fof(f3425,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3424])).

fof(f3424,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3324])).

fof(f3324,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f6212,plain,
    ( g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK266,sK264))
    | g1_pre_topc(u1_struct_0(sK264),u1_pre_topc(sK264)) != k2_tsep_1(sK263,sK265,k1_tsep_1(sK263,sK264,sK266)) ),
    inference(cnf_transformation,[],[f5066])).

fof(f8921,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK266,sK265)
      | ~ m1_pre_topc(sK265,X1)
      | ~ m1_pre_topc(sK264,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8920,f6204])).

fof(f8920,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK266,sK265)
      | ~ m1_pre_topc(sK265,X1)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8919,f6206])).

fof(f8919,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK266,sK265)
      | ~ m1_pre_topc(sK265,X1)
      | v2_struct_0(sK265)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f8916,f6210])).

fof(f8916,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(sK266,sK265)
      | ~ m1_pre_topc(sK264,sK265)
      | ~ m1_pre_topc(sK265,X1)
      | v2_struct_0(sK265)
      | ~ m1_pre_topc(sK264,X1)
      | v2_struct_0(sK264)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f8909,f6409])).

fof(f8909,plain,
    ( r1_tsep_1(sK265,sK264)
    | ~ r1_tsep_1(sK266,sK265) ),
    inference(resolution,[],[f8908,f6225])).

fof(f6225,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5074])).

fof(f6211,plain,
    ( r1_tsep_1(sK266,sK265)
    | r1_tsep_1(sK265,sK266) ),
    inference(cnf_transformation,[],[f5066])).
%------------------------------------------------------------------------------
