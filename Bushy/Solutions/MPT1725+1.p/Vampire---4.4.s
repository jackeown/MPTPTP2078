%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t34_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:13 EDT 2019

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  376 (2787 expanded)
%              Number of leaves         :   51 (1224 expanded)
%              Depth                    :   33
%              Number of atoms          : 2051 (42312 expanded)
%              Number of equality atoms :   26 (  83 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10782,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f171,f178,f179,f262,f267,f274,f954,f1623,f1684,f1753,f2212,f2495,f2692,f2821,f2844,f3158,f3200,f3215,f3926,f4008,f4016,f4133,f4218,f5246,f7166,f10389,f10399,f10781])).

fof(f10781,plain,
    ( ~ spl8_2
    | ~ spl8_8
    | spl8_23
    | spl8_97
    | ~ spl8_98
    | spl8_309
    | ~ spl8_326
    | spl8_363
    | ~ spl8_364 ),
    inference(avatar_contradiction_clause,[],[f10780])).

fof(f10780,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_309
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10779,f93])).

fof(f93,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
          | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
        & m1_pre_topc(sK2,sK3) )
      | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
          | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f73,f72,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                        & m1_pre_topc(X2,X3) )
                      | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
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
                  ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,sK1),X2)
                      | r1_tsep_1(k2_tsep_1(X0,sK1,X3),X2) )
                    & m1_pre_topc(X2,X3) )
                  | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),sK1)
                      | r1_tsep_1(k2_tsep_1(X0,X3,X2),sK1) )
                    & m1_pre_topc(sK1,X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                    | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                  & m1_pre_topc(X2,X3) )
                | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                    | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                  & m1_pre_topc(X1,X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),sK2)
                  | r1_tsep_1(k2_tsep_1(X0,X1,X3),sK2) )
                & m1_pre_topc(sK2,X3) )
              | ( ( r1_tsep_1(k2_tsep_1(X0,sK2,X3),X1)
                  | r1_tsep_1(k2_tsep_1(X0,X3,sK2),X1) )
                & m1_pre_topc(X1,X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
              & m1_pre_topc(X2,X3) )
            | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
              & m1_pre_topc(X1,X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ( r1_tsep_1(k2_tsep_1(X0,sK3,X1),X2)
              | r1_tsep_1(k2_tsep_1(X0,X1,sK3),X2) )
            & m1_pre_topc(X2,sK3) )
          | ( ( r1_tsep_1(k2_tsep_1(X0,X2,sK3),X1)
              | r1_tsep_1(k2_tsep_1(X0,sK3,X2),X1) )
            & m1_pre_topc(X1,sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                        & ( m1_pre_topc(X1,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t34_tmap_1)).

fof(f10779,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_309
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10778,f89])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

fof(f10778,plain,
    ( v2_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_309
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10777,f90])).

fof(f90,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f10777,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_309
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10761,f7876])).

fof(f7876,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7875,f3190])).

fof(f3190,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl8_363 ),
    inference(avatar_component_clause,[],[f3189])).

fof(f3189,plain,
    ( spl8_363
  <=> ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_363])])).

fof(f7875,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7874,f3196])).

fof(f3196,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl8_364 ),
    inference(avatar_component_clause,[],[f3195])).

fof(f3195,plain,
    ( spl8_364
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_364])])).

fof(f7874,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7873,f912])).

fof(f912,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f911])).

fof(f911,plain,
    ( spl8_97
  <=> ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f7873,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7864,f918])).

fof(f918,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl8_98 ),
    inference(avatar_component_clause,[],[f917])).

fof(f917,plain,
    ( spl8_98
  <=> m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f7864,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(resolution,[],[f7848,f899])).

fof(f899,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f898,f84])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f898,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f897,f86])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f897,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f108,f85])).

fof(f85,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t22_tmap_1)).

fof(f7848,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7847,f3190])).

fof(f7847,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f7839,f3196])).

fof(f7839,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_2
    | ~ spl8_23
    | ~ spl8_97
    | ~ spl8_98
    | ~ spl8_326 ),
    inference(resolution,[],[f7485,f3171])).

fof(f3171,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3170,f84])).

fof(f3170,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3169,f85])).

fof(f3169,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3168,f86])).

fof(f3168,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3167,f89])).

fof(f3167,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3166,f90])).

fof(f3166,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3165,f87])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

fof(f3165,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3164,f88])).

fof(f88,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f3164,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3159,f261])).

fof(f261,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl8_23
  <=> ~ r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f3159,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_326 ),
    inference(superposition,[],[f107,f3144])).

fof(f3144,plain,
    ( k2_tsep_1(sK0,sK1,sK2) = k2_tsep_1(sK0,sK2,sK1)
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3143,f90])).

fof(f3143,plain,
    ( k2_tsep_1(sK0,sK1,sK2) = k2_tsep_1(sK0,sK2,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3109,f93])).

fof(f3109,plain,
    ( r1_tsep_1(sK1,sK2)
    | k2_tsep_1(sK0,sK1,sK2) = k2_tsep_1(sK0,sK2,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_326 ),
    inference(resolution,[],[f3099,f89])).

fof(f3099,plain,
    ( ! [X9] :
        ( v2_struct_0(X9)
        | r1_tsep_1(sK1,X9)
        | k2_tsep_1(sK0,X9,sK1) = k2_tsep_1(sK0,sK1,X9)
        | ~ m1_pre_topc(X9,sK0) )
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3090,f88])).

fof(f3090,plain,
    ( ! [X9] :
        ( k2_tsep_1(sK0,X9,sK1) = k2_tsep_1(sK0,sK1,X9)
        | r1_tsep_1(sK1,X9)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0) )
    | ~ spl8_326 ),
    inference(resolution,[],[f2820,f87])).

fof(f2820,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl8_326 ),
    inference(avatar_component_clause,[],[f2819])).

fof(f2819,plain,
    ( spl8_326
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,X1)
        | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_326])])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t30_tsep_1)).

fof(f7485,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK3)) )
    | ~ spl8_2
    | ~ spl8_97
    | ~ spl8_98 ),
    inference(subsumption_resolution,[],[f7484,f87])).

fof(f7484,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK3)) )
    | ~ spl8_2
    | ~ spl8_97
    | ~ spl8_98 ),
    inference(subsumption_resolution,[],[f7483,f88])).

fof(f7483,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK3)) )
    | ~ spl8_2
    | ~ spl8_97
    | ~ spl8_98 ),
    inference(subsumption_resolution,[],[f7482,f912])).

fof(f7482,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK3)) )
    | ~ spl8_2
    | ~ spl8_98 ),
    inference(subsumption_resolution,[],[f7464,f918])).

fof(f7464,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK1)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,k2_tsep_1(sK0,sK2,sK3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f151,f2409])).

fof(f2409,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2408,f84])).

fof(f2408,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2407,f86])).

fof(f2407,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f117,f85])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t23_tmap_1)).

fof(f151,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl8_2
  <=> r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f10761,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | ~ spl8_8
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(superposition,[],[f10406,f7091])).

fof(f7091,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f7090,f92])).

fof(f92,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f7090,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f7070,f91])).

fof(f91,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f7070,plain,
    ( k2_tsep_1(sK0,sK2,sK3) = k2_tsep_1(sK0,sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(resolution,[],[f3100,f2467])).

fof(f2467,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl8_309 ),
    inference(avatar_component_clause,[],[f2466])).

fof(f2466,plain,
    ( spl8_309
  <=> ~ r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_309])])).

fof(f3100,plain,
    ( ! [X10] :
        ( r1_tsep_1(sK2,X10)
        | k2_tsep_1(sK0,X10,sK2) = k2_tsep_1(sK0,sK2,X10)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0) )
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3091,f90])).

fof(f3091,plain,
    ( ! [X10] :
        ( k2_tsep_1(sK0,X10,sK2) = k2_tsep_1(sK0,sK2,X10)
        | r1_tsep_1(sK2,X10)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0) )
    | ~ spl8_326 ),
    inference(resolution,[],[f2820,f89])).

fof(f10406,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,X0),k2_tsep_1(sK0,sK3,X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(sK1,X0) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f10405,f87])).

fof(f10405,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK1)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),k2_tsep_1(sK0,sK3,X0)) )
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f10403,f88])).

fof(f10403,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | m1_pre_topc(k2_tsep_1(sK0,sK1,X0),k2_tsep_1(sK0,sK3,X0)) )
    | ~ spl8_8 ),
    inference(resolution,[],[f170,f5066])).

fof(f5066,plain,(
    ! [X21,X22] :
      ( ~ m1_pre_topc(X21,sK3)
      | r1_tsep_1(X21,X22)
      | ~ m1_pre_topc(X22,sK0)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X21,sK0)
      | v2_struct_0(X21)
      | m1_pre_topc(k2_tsep_1(sK0,X21,X22),k2_tsep_1(sK0,sK3,X22)) ) ),
    inference(subsumption_resolution,[],[f5053,f92])).

fof(f5053,plain,(
    ! [X21,X22] :
      ( r1_tsep_1(X21,X22)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(X21,sK3)
      | ~ m1_pre_topc(X22,sK0)
      | v2_struct_0(X22)
      | ~ m1_pre_topc(X21,sK0)
      | v2_struct_0(X21)
      | m1_pre_topc(k2_tsep_1(sK0,X21,X22),k2_tsep_1(sK0,sK3,X22)) ) ),
    inference(resolution,[],[f3083,f91])).

fof(f3083,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,X0,X2),k2_tsep_1(sK0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f3082,f84])).

fof(f3082,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | m1_pre_topc(k2_tsep_1(sK0,X0,X2),k2_tsep_1(sK0,X1,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3081,f86])).

fof(f3081,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | m1_pre_topc(k2_tsep_1(sK0,X0,X2),k2_tsep_1(sK0,X1,X2))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f113,f85])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t32_tmap_1)).

fof(f170,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_8
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f10399,plain,
    ( spl8_23
    | ~ spl8_326
    | ~ spl8_358
    | spl8_363
    | ~ spl8_364
    | spl8_423 ),
    inference(avatar_contradiction_clause,[],[f10398])).

fof(f10398,plain,
    ( $false
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_358
    | ~ spl8_363
    | ~ spl8_364
    | ~ spl8_423 ),
    inference(subsumption_resolution,[],[f10397,f3922])).

fof(f3922,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_423 ),
    inference(avatar_component_clause,[],[f3921])).

fof(f3921,plain,
    ( spl8_423
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_423])])).

fof(f10397,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_358
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10396,f3190])).

fof(f10396,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_358
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f4409,f3196])).

fof(f4409,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_358 ),
    inference(resolution,[],[f4245,f3171])).

fof(f4245,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_358 ),
    inference(subsumption_resolution,[],[f4244,f87])).

fof(f4244,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_358 ),
    inference(subsumption_resolution,[],[f4243,f88])).

fof(f4243,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_358 ),
    inference(subsumption_resolution,[],[f4242,f91])).

fof(f4242,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_358 ),
    inference(subsumption_resolution,[],[f4222,f92])).

fof(f4222,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_358 ),
    inference(resolution,[],[f3157,f1533])).

fof(f1533,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1532,f84])).

fof(f1532,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1531,f86])).

fof(f1531,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f115,f85])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3157,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl8_358 ),
    inference(avatar_component_clause,[],[f3156])).

fof(f3156,plain,
    ( spl8_358
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_358])])).

fof(f10389,plain,
    ( ~ spl8_10
    | spl8_23
    | spl8_195
    | ~ spl8_196
    | ~ spl8_326
    | ~ spl8_356
    | ~ spl8_360
    | spl8_363
    | ~ spl8_364 ),
    inference(avatar_contradiction_clause,[],[f10388])).

fof(f10388,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_23
    | ~ spl8_195
    | ~ spl8_196
    | ~ spl8_326
    | ~ spl8_356
    | ~ spl8_360
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f10387,f4590])).

fof(f4590,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_195
    | ~ spl8_196
    | ~ spl8_356
    | ~ spl8_360
    | ~ spl8_363
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f4589,f3190])).

fof(f4589,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_195
    | ~ spl8_196
    | ~ spl8_356
    | ~ spl8_360
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f4588,f3196])).

fof(f4588,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_195
    | ~ spl8_196
    | ~ spl8_356
    | ~ spl8_360 ),
    inference(subsumption_resolution,[],[f4587,f1635])).

fof(f1635,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_195 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1634,plain,
    ( spl8_195
  <=> ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_195])])).

fof(f4587,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_196
    | ~ spl8_356
    | ~ spl8_360 ),
    inference(subsumption_resolution,[],[f4570,f1641])).

fof(f1641,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl8_196 ),
    inference(avatar_component_clause,[],[f1640])).

fof(f1640,plain,
    ( spl8_196
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_196])])).

fof(f4570,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_356
    | ~ spl8_360 ),
    inference(resolution,[],[f4566,f1082])).

fof(f1082,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1081,f84])).

fof(f1081,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ r1_tsep_1(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1080,f86])).

fof(f1080,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f109,f85])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4566,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),k2_tsep_1(sK0,sK1,sK2))
    | ~ spl8_356
    | ~ spl8_360 ),
    inference(forward_demodulation,[],[f3187,f3151])).

fof(f3151,plain,
    ( k2_tsep_1(sK0,sK1,sK3) = k2_tsep_1(sK0,sK3,sK1)
    | ~ spl8_356 ),
    inference(avatar_component_clause,[],[f3150])).

fof(f3150,plain,
    ( spl8_356
  <=> k2_tsep_1(sK0,sK1,sK3) = k2_tsep_1(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_356])])).

fof(f3187,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),k2_tsep_1(sK0,sK1,sK2))
    | ~ spl8_360 ),
    inference(avatar_component_clause,[],[f3186])).

fof(f3186,plain,
    ( spl8_360
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_360])])).

fof(f10387,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_10
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_356 ),
    inference(forward_demodulation,[],[f10386,f3144])).

fof(f10386,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_10
    | ~ spl8_23
    | ~ spl8_356 ),
    inference(subsumption_resolution,[],[f10385,f261])).

fof(f10385,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK1)
    | ~ spl8_10
    | ~ spl8_356 ),
    inference(subsumption_resolution,[],[f10384,f87])).

fof(f10384,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ spl8_10
    | ~ spl8_356 ),
    inference(subsumption_resolution,[],[f10376,f88])).

fof(f10376,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK2,sK1)
    | ~ spl8_10
    | ~ spl8_356 ),
    inference(superposition,[],[f10319,f3151])).

fof(f10319,plain,
    ( ! [X2] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK2,X2),k2_tsep_1(sK0,sK3,X2))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | r1_tsep_1(sK2,X2) )
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f10318,f89])).

fof(f10318,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK2,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(sK2)
        | m1_pre_topc(k2_tsep_1(sK0,sK2,X2),k2_tsep_1(sK0,sK3,X2)) )
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f10309,f90])).

fof(f10309,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK2,X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | m1_pre_topc(k2_tsep_1(sK0,sK2,X2),k2_tsep_1(sK0,sK3,X2)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f5066,f177])).

fof(f177,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f7166,plain,
    ( ~ spl8_0
    | spl8_3
    | spl8_309
    | ~ spl8_326 ),
    inference(avatar_contradiction_clause,[],[f7165])).

fof(f7165,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f7144,f148])).

fof(f148,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_3
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f7144,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ spl8_0
    | ~ spl8_309
    | ~ spl8_326 ),
    inference(backward_demodulation,[],[f7091,f145])).

fof(f145,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_0
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f5246,plain,
    ( ~ spl8_10
    | spl8_23
    | ~ spl8_326
    | spl8_363
    | ~ spl8_364
    | ~ spl8_436 ),
    inference(avatar_contradiction_clause,[],[f5245])).

fof(f5245,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_23
    | ~ spl8_326
    | ~ spl8_363
    | ~ spl8_364
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5244,f3179])).

fof(f3179,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3178,f84])).

fof(f3178,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3177,f85])).

fof(f3177,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3176,f86])).

fof(f3176,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3175,f89])).

fof(f3175,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3174,f90])).

fof(f3174,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3173,f87])).

fof(f3173,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3172,f88])).

fof(f3172,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_23
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3160,f261])).

fof(f3160,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | r1_tsep_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_326 ),
    inference(superposition,[],[f106,f3144])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5244,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_363
    | ~ spl8_364
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5243,f3190])).

fof(f5243,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_364
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5242,f3196])).

fof(f5242,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5241,f89])).

fof(f5241,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5232,f90])).

fof(f5232,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(resolution,[],[f5227,f899])).

fof(f5227,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5226,f89])).

fof(f5226,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(subsumption_resolution,[],[f5221,f90])).

fof(f5221,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(sK2)
    | ~ spl8_10
    | ~ spl8_436 ),
    inference(resolution,[],[f3999,f177])).

fof(f3999,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X3,sK0)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
        | v2_struct_0(X3) )
    | ~ spl8_436 ),
    inference(avatar_component_clause,[],[f3998])).

fof(f3998,plain,
    ( spl8_436
  <=> ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK3)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_436])])).

fof(f4218,plain,
    ( ~ spl8_4
    | spl8_7
    | ~ spl8_356 ),
    inference(avatar_contradiction_clause,[],[f4217])).

fof(f4217,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_356 ),
    inference(subsumption_resolution,[],[f3328,f157])).

fof(f157,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_4
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f3328,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ spl8_7
    | ~ spl8_356 ),
    inference(backward_demodulation,[],[f3151,f160])).

fof(f160,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_7
  <=> ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f4133,plain,
    ( ~ spl8_8
    | ~ spl8_308 ),
    inference(avatar_contradiction_clause,[],[f4132])).

fof(f4132,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f4131,f93])).

fof(f4131,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_8
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f4130,f87])).

fof(f4130,plain,
    ( v2_struct_0(sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ spl8_8
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f4124,f88])).

fof(f4124,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ spl8_8
    | ~ spl8_308 ),
    inference(resolution,[],[f3784,f170])).

fof(f3784,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,sK2) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3783,f91])).

fof(f3783,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,sK2) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3782,f92])).

fof(f3782,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,sK2) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3781,f89])).

fof(f3781,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,sK2) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3749,f90])).

fof(f3749,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | r1_tsep_1(X4,sK2) )
    | ~ spl8_308 ),
    inference(resolution,[],[f2470,f2409])).

fof(f2470,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl8_308 ),
    inference(avatar_component_clause,[],[f2469])).

fof(f2469,plain,
    ( spl8_308
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_308])])).

fof(f4016,plain,(
    ~ spl8_362 ),
    inference(avatar_contradiction_clause,[],[f4015])).

fof(f4015,plain,
    ( $false
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4014,f84])).

fof(f4014,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4013,f86])).

fof(f4013,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4012,f87])).

fof(f4012,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4011,f88])).

fof(f4011,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4010,f89])).

fof(f4010,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(subsumption_resolution,[],[f4009,f90])).

fof(f4009,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_362 ),
    inference(resolution,[],[f3193,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',dt_k2_tsep_1)).

fof(f3193,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl8_362 ),
    inference(avatar_component_clause,[],[f3192])).

fof(f3192,plain,
    ( spl8_362
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_362])])).

fof(f4008,plain,
    ( spl8_362
    | spl8_436
    | ~ spl8_364
    | ~ spl8_422 ),
    inference(avatar_split_clause,[],[f4007,f3924,f3195,f3998,f3192])).

fof(f3924,plain,
    ( spl8_422
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_422])])).

fof(f4007,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X5) )
    | ~ spl8_364
    | ~ spl8_422 ),
    inference(subsumption_resolution,[],[f4006,f91])).

fof(f4006,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X5) )
    | ~ spl8_364
    | ~ spl8_422 ),
    inference(subsumption_resolution,[],[f4005,f92])).

fof(f4005,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X5) )
    | ~ spl8_364
    | ~ spl8_422 ),
    inference(subsumption_resolution,[],[f3939,f3196])).

fof(f3939,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK3)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X5) )
    | ~ spl8_422 ),
    inference(resolution,[],[f3925,f2604])).

fof(f2604,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | r1_tsep_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2603,f84])).

fof(f2603,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2602,f86])).

fof(f2602,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(sK0)
      | ~ r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f118,f85])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3925,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_422 ),
    inference(avatar_component_clause,[],[f3924])).

fof(f3926,plain,
    ( spl8_422
    | spl8_362
    | spl8_23
    | ~ spl8_308
    | ~ spl8_326
    | ~ spl8_364 ),
    inference(avatar_split_clause,[],[f3919,f3195,f2819,f2469,f260,f3192,f3924])).

fof(f3919,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_23
    | ~ spl8_308
    | ~ spl8_326
    | ~ spl8_364 ),
    inference(subsumption_resolution,[],[f3914,f3196])).

fof(f3914,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl8_23
    | ~ spl8_308
    | ~ spl8_326 ),
    inference(resolution,[],[f3764,f3179])).

fof(f3764,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3763,f89])).

fof(f3763,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3762,f90])).

fof(f3762,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3761,f91])).

fof(f3761,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f3745,f92])).

fof(f3745,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK3) )
    | ~ spl8_308 ),
    inference(resolution,[],[f2470,f1533])).

fof(f3215,plain,(
    spl8_365 ),
    inference(avatar_contradiction_clause,[],[f3214])).

fof(f3214,plain,
    ( $false
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3213,f84])).

fof(f3213,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3212,f86])).

fof(f3212,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3211,f87])).

fof(f3211,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3210,f88])).

fof(f3210,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3209,f89])).

fof(f3209,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(subsumption_resolution,[],[f3208,f90])).

fof(f3208,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_365 ),
    inference(resolution,[],[f3199,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f3199,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl8_365 ),
    inference(avatar_component_clause,[],[f3198])).

fof(f3198,plain,
    ( spl8_365
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_365])])).

fof(f3200,plain,
    ( spl8_360
    | spl8_362
    | ~ spl8_365
    | ~ spl8_6
    | spl8_23
    | spl8_209
    | ~ spl8_210
    | ~ spl8_326 ),
    inference(avatar_split_clause,[],[f3180,f2819,f1709,f1703,f260,f162,f3198,f3192,f3186])).

fof(f162,plain,
    ( spl8_6
  <=> r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1703,plain,
    ( spl8_209
  <=> ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_209])])).

fof(f1709,plain,
    ( spl8_210
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_210])])).

fof(f3180,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),k2_tsep_1(sK0,sK1,sK2))
    | ~ spl8_6
    | ~ spl8_23
    | ~ spl8_209
    | ~ spl8_210
    | ~ spl8_326 ),
    inference(resolution,[],[f3179,f2884])).

fof(f2884,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),X5) )
    | ~ spl8_6
    | ~ spl8_209
    | ~ spl8_210 ),
    inference(subsumption_resolution,[],[f2883,f89])).

fof(f2883,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),X5) )
    | ~ spl8_6
    | ~ spl8_209
    | ~ spl8_210 ),
    inference(subsumption_resolution,[],[f2882,f90])).

fof(f2882,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),X5) )
    | ~ spl8_6
    | ~ spl8_209
    | ~ spl8_210 ),
    inference(subsumption_resolution,[],[f2881,f1704])).

fof(f1704,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | ~ spl8_209 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f2881,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),X5) )
    | ~ spl8_6
    | ~ spl8_210 ),
    inference(subsumption_resolution,[],[f2856,f1710])).

fof(f1710,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ spl8_210 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f2856,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
        | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),X5) )
    | ~ spl8_6 ),
    inference(resolution,[],[f163,f2604])).

fof(f163,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f3158,plain,
    ( spl8_356
    | spl8_358
    | ~ spl8_326 ),
    inference(avatar_split_clause,[],[f3145,f2819,f3156,f3150])).

fof(f3145,plain,
    ( r1_tsep_1(sK1,sK3)
    | k2_tsep_1(sK0,sK1,sK3) = k2_tsep_1(sK0,sK3,sK1)
    | ~ spl8_326 ),
    inference(subsumption_resolution,[],[f3110,f92])).

fof(f3110,plain,
    ( r1_tsep_1(sK1,sK3)
    | k2_tsep_1(sK0,sK1,sK3) = k2_tsep_1(sK0,sK3,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_326 ),
    inference(resolution,[],[f3099,f91])).

fof(f2844,plain,(
    ~ spl8_324 ),
    inference(avatar_contradiction_clause,[],[f2843])).

fof(f2843,plain,
    ( $false
    | ~ spl8_324 ),
    inference(subsumption_resolution,[],[f2830,f92])).

fof(f2830,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl8_324 ),
    inference(resolution,[],[f2817,f91])).

fof(f2817,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl8_324 ),
    inference(avatar_component_clause,[],[f2816])).

fof(f2816,plain,
    ( spl8_324
  <=> ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_324])])).

fof(f2821,plain,
    ( spl8_324
    | spl8_326 ),
    inference(avatar_split_clause,[],[f2814,f2819,f2816])).

fof(f2814,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f2813,f84])).

fof(f2813,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2812,f86])).

fof(f2812,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | k2_tsep_1(sK0,X0,X1) = k2_tsep_1(sK0,X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f110,f85])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3)
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3)
                      | ( ( r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          | r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          | r1_tsep_1(X1,X2) ) ) )
                    & ( k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1)
                      | r1_tsep_1(X1,X2) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
                 => ( ( ( ( ~ r1_tsep_1(X1,k2_tsep_1(X0,X2,X3))
                          & ~ r1_tsep_1(X2,X3) )
                        | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                          & ~ r1_tsep_1(X1,X2) ) )
                     => k2_tsep_1(X0,X1,k2_tsep_1(X0,X2,X3)) = k2_tsep_1(X0,k2_tsep_1(X0,X1,X2),X3) )
                    & ( ~ r1_tsep_1(X1,X2)
                     => k2_tsep_1(X0,X1,X2) = k2_tsep_1(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',t29_tsep_1)).

fof(f2692,plain,(
    ~ spl8_208 ),
    inference(avatar_contradiction_clause,[],[f2691])).

fof(f2691,plain,
    ( $false
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2690,f84])).

fof(f2690,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2689,f86])).

fof(f2689,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2688,f91])).

fof(f2688,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2687,f92])).

fof(f2687,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2686,f87])).

fof(f2686,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(subsumption_resolution,[],[f2685,f88])).

fof(f2685,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_208 ),
    inference(resolution,[],[f1707,f132])).

fof(f1707,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | ~ spl8_208 ),
    inference(avatar_component_clause,[],[f1706])).

fof(f1706,plain,
    ( spl8_208
  <=> v2_struct_0(k2_tsep_1(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_208])])).

fof(f2495,plain,
    ( ~ spl8_10
    | ~ spl8_308 ),
    inference(avatar_contradiction_clause,[],[f2494])).

fof(f2494,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f2493,f177])).

fof(f2493,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f2492,f89])).

fof(f2492,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f2491,f90])).

fof(f2491,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f2490,f91])).

fof(f2490,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_308 ),
    inference(subsumption_resolution,[],[f2482,f92])).

fof(f2482,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ spl8_308 ),
    inference(resolution,[],[f2470,f899])).

fof(f2212,plain,(
    ~ spl8_194 ),
    inference(avatar_contradiction_clause,[],[f2211])).

fof(f2211,plain,
    ( $false
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2210,f84])).

fof(f2210,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2209,f86])).

fof(f2209,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2208,f87])).

fof(f2208,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2207,f88])).

fof(f2207,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2206,f91])).

fof(f2206,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(subsumption_resolution,[],[f2205,f92])).

fof(f2205,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_194 ),
    inference(resolution,[],[f1638,f132])).

fof(f1638,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | ~ spl8_194 ),
    inference(avatar_component_clause,[],[f1637])).

fof(f1637,plain,
    ( spl8_194
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_194])])).

fof(f1753,plain,(
    spl8_211 ),
    inference(avatar_contradiction_clause,[],[f1752])).

fof(f1752,plain,
    ( $false
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1751,f84])).

fof(f1751,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1750,f86])).

fof(f1750,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1749,f91])).

fof(f1749,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1748,f92])).

fof(f1748,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1747,f87])).

fof(f1747,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1746,f88])).

fof(f1746,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_211 ),
    inference(resolution,[],[f1713,f134])).

fof(f1713,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ spl8_211 ),
    inference(avatar_component_clause,[],[f1712])).

fof(f1712,plain,
    ( spl8_211
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_211])])).

fof(f1684,plain,(
    spl8_197 ),
    inference(avatar_contradiction_clause,[],[f1683])).

fof(f1683,plain,
    ( $false
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1682,f84])).

fof(f1682,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1681,f86])).

fof(f1681,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1680,f87])).

fof(f1680,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1679,f88])).

fof(f1679,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1678,f91])).

fof(f1678,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1677,f92])).

fof(f1677,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_197 ),
    inference(resolution,[],[f1644,f134])).

fof(f1644,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl8_197 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f1643,plain,
    ( spl8_197
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_197])])).

fof(f1623,plain,(
    ~ spl8_96 ),
    inference(avatar_contradiction_clause,[],[f1622])).

fof(f1622,plain,
    ( $false
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1621,f84])).

fof(f1621,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1620,f86])).

fof(f1620,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1619,f89])).

fof(f1619,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1618,f90])).

fof(f1618,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1617,f91])).

fof(f1617,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(subsumption_resolution,[],[f1616,f92])).

fof(f1616,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_96 ),
    inference(resolution,[],[f915,f132])).

fof(f915,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | ~ spl8_96 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl8_96
  <=> v2_struct_0(k2_tsep_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f954,plain,(
    spl8_99 ),
    inference(avatar_contradiction_clause,[],[f953])).

fof(f953,plain,
    ( $false
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f952,f84])).

fof(f952,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f951,f86])).

fof(f951,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f950,f89])).

fof(f950,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f949,f90])).

fof(f949,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f948,f91])).

fof(f948,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(subsumption_resolution,[],[f947,f92])).

fof(f947,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_99 ),
    inference(resolution,[],[f921,f134])).

fof(f921,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ spl8_99 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl8_99
  <=> ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f274,plain,(
    spl8_21 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f271,f86])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_21 ),
    inference(resolution,[],[f270,f88])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_21 ),
    inference(resolution,[],[f268,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',dt_m1_pre_topc)).

fof(f268,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_21 ),
    inference(resolution,[],[f255,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',dt_l1_pre_topc)).

fof(f255,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl8_21
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f267,plain,(
    spl8_19 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f265,f86])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f264,f90])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_19 ),
    inference(resolution,[],[f263,f104])).

fof(f263,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl8_19 ),
    inference(resolution,[],[f249,f101])).

fof(f249,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl8_19
  <=> ~ l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f262,plain,
    ( ~ spl8_19
    | ~ spl8_21
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f243,f260,f254,f248])).

fof(f243,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2) ),
    inference(resolution,[],[f127,f93])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t34_tmap_1.p',symmetry_r1_tsep_1)).

fof(f179,plain,
    ( spl8_8
    | spl8_10 ),
    inference(avatar_split_clause,[],[f94,f176,f169])).

fof(f94,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f178,plain,
    ( spl8_0
    | spl8_2
    | spl8_10 ),
    inference(avatar_split_clause,[],[f95,f176,f150,f144])).

fof(f95,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f74])).

fof(f171,plain,
    ( spl8_8
    | spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f96,f162,f156,f169])).

fof(f96,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f74])).

fof(f164,plain,
    ( spl8_0
    | spl8_2
    | spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f97,f162,f156,f150,f144])).

fof(f97,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
