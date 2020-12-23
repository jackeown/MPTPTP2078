%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (1390 expanded)
%              Number of leaves         :   18 ( 608 expanded)
%              Depth                    :   22
%              Number of atoms          :  860 (18027 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f950,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f86,f96,f304,f609,f625,f916,f949])).

fof(f949,plain,
    ( spl7_2
    | ~ spl7_4
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f948])).

fof(f948,plain,
    ( $false
    | spl7_2
    | ~ spl7_4
    | spl7_17 ),
    inference(subsumption_resolution,[],[f947,f172])).

fof(f172,plain,(
    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f169,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( ( r1_tsep_1(sK6,sK5)
          | r1_tsep_1(sK6,sK4) )
        & ~ r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) )
      | sP0(sK6,sK5,sK4,sK3) )
    & ~ r1_tsep_1(sK4,sK5)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0) )
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
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK3,X1,X2)) )
                    | sP0(X3,X2,X1,sK3) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(sK3,X1,X2)) )
                  | sP0(X3,X2,X1,sK3) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK3)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK4) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(sK3,sK4,X2)) )
                | sP0(X3,X2,sK4,sK3) )
              & ~ r1_tsep_1(sK4,X2)
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK4) )
                & ~ r1_tsep_1(X3,k2_tsep_1(sK3,sK4,X2)) )
              | sP0(X3,X2,sK4,sK3) )
            & ~ r1_tsep_1(sK4,X2)
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,sK5)
                | r1_tsep_1(X3,sK4) )
              & ~ r1_tsep_1(X3,k2_tsep_1(sK3,sK4,sK5)) )
            | sP0(X3,sK5,sK4,sK3) )
          & ~ r1_tsep_1(sK4,sK5)
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(X3,sK5)
              | r1_tsep_1(X3,sK4) )
            & ~ r1_tsep_1(X3,k2_tsep_1(sK3,sK4,sK5)) )
          | sP0(X3,sK5,sK4,sK3) )
        & ~ r1_tsep_1(sK4,sK5)
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(sK6,sK5)
            | r1_tsep_1(sK6,sK4) )
          & ~ r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) )
        | sP0(sK6,sK5,sK4,sK3) )
      & ~ r1_tsep_1(sK4,sK5)
      & m1_pre_topc(sK6,sK3)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

% (25431)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0) )
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
    inference(definition_folding,[],[f7,f14])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f169,plain,
    ( v2_struct_0(sK4)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) ),
    inference(resolution,[],[f137,f37])).

fof(f37,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | m1_pre_topc(k2_tsep_1(sK3,X1,sK5),sK3) ) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f134,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | v2_struct_0(sK5)
      | m1_pre_topc(k2_tsep_1(sK3,X1,sK5),sK3) ) ),
    inference(resolution,[],[f98,f39])).

fof(f39,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ m1_pre_topc(X2,sK3)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | m1_pre_topc(k2_tsep_1(sK3,X3,X2),sK3) ) ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sP2(sK3,X0,X1)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f67,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | sP2(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | sP2(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f13,f18])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f35,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f947,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | spl7_2
    | ~ spl7_4
    | spl7_17 ),
    inference(subsumption_resolution,[],[f946,f76])).

fof(f76,plain,
    ( ~ r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f946,plain,
    ( r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_4
    | spl7_17 ),
    inference(subsumption_resolution,[],[f945,f288])).

fof(f288,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl7_17
  <=> v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f945,plain,
    ( v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f932,f233])).

fof(f233,plain,(
    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5) ),
    inference(subsumption_resolution,[],[f232,f36])).

fof(f232,plain,
    ( v2_struct_0(sK4)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5) ),
    inference(subsumption_resolution,[],[f231,f37])).

fof(f231,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5) ),
    inference(subsumption_resolution,[],[f230,f38])).

fof(f230,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5) ),
    inference(subsumption_resolution,[],[f228,f39])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5) ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X8,X9] :
      ( r1_tsep_1(X8,X9)
      | ~ m1_pre_topc(X9,sK3)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X8,sK3)
      | v2_struct_0(X8)
      | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9) ) ),
    inference(global_subsumption,[],[f35,f65])).

fof(f65,plain,(
    ! [X8,X9] :
      ( r1_tsep_1(X8,X9)
      | ~ m1_pre_topc(X9,sK3)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X8,sK3)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK3)
      | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9) ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X8,X9] :
      ( r1_tsep_1(X8,X9)
      | ~ m1_pre_topc(X9,sK3)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X8,sK3)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK3)
      | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f34,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f932,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK5)
        | v2_struct_0(X0)
        | r1_tsep_1(sK6,X0)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f931,f38])).

fof(f931,plain,
    ( ! [X0] :
        ( v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(sK6,X0)
        | ~ m1_pre_topc(X0,sK5) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f930,f39])).

fof(f930,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(sK6,X0)
        | ~ m1_pre_topc(X0,sK5) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f929,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f929,plain,
    ( ! [X0] :
        ( v2_struct_0(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(sK6,X0)
        | ~ m1_pre_topc(X0,sK5) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f925,f41])).

fof(f41,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK6,sK3)
        | v2_struct_0(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(sK6,X0)
        | ~ m1_pre_topc(X0,sK5) )
    | ~ spl7_4 ),
    inference(resolution,[],[f85,f350])).

fof(f350,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tsep_1(X5,X4)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | r1_tsep_1(X5,X3)
      | ~ m1_pre_topc(X3,X4) ) ),
    inference(resolution,[],[f62,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_tsep_1(X1,X0)
        & ~ r1_tsep_1(X0,X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X3] :
      ( ( ~ r1_tsep_1(X3,X2)
        & ~ r1_tsep_1(X2,X3) )
      | ~ sP1(X2,X3) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X2,X3] :
      ( ( ~ r1_tsep_1(X3,X2)
        & ~ r1_tsep_1(X2,X3) )
      | ~ sP1(X2,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f62,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4)
      | ~ m1_pre_topc(X5,X3)
      | ~ m1_pre_topc(X4,sK3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(X5)
      | r1_tsep_1(X4,X5) ) ),
    inference(global_subsumption,[],[f35,f61])).

fof(f61,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4)
      | ~ m1_pre_topc(X5,X3)
      | ~ m1_pre_topc(X4,sK3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(sK3)
      | r1_tsep_1(X4,X5) ) ),
    inference(subsumption_resolution,[],[f56,f33])).

fof(f56,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X4)
      | ~ m1_pre_topc(X5,X3)
      | ~ m1_pre_topc(X4,sK3)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,sK3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X5,sK3)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(sK3)
      | r1_tsep_1(X4,X5)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | sP1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | sP1(X2,X3)
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
    inference(definition_folding,[],[f11,f16])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f85,plain,
    ( r1_tsep_1(sK6,sK5)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_4
  <=> r1_tsep_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f916,plain,
    ( spl7_2
    | ~ spl7_3
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f915])).

fof(f915,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | spl7_17 ),
    inference(subsumption_resolution,[],[f914,f172])).

fof(f914,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | spl7_2
    | ~ spl7_3
    | spl7_17 ),
    inference(subsumption_resolution,[],[f913,f76])).

fof(f913,plain,
    ( r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_3
    | spl7_17 ),
    inference(subsumption_resolution,[],[f912,f288])).

fof(f912,plain,
    ( v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_3 ),
    inference(resolution,[],[f911,f131])).

fof(f131,plain,(
    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4) ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f130,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4) ),
    inference(subsumption_resolution,[],[f129,f38])).

fof(f129,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK5,sK3)
    | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4) ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X0] :
      ( r1_tsep_1(sK4,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK3)
      | m1_pre_topc(k2_tsep_1(sK3,sK4,X0),sK4) ) ),
    inference(subsumption_resolution,[],[f117,f36])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | r1_tsep_1(sK4,X0)
      | v2_struct_0(sK4)
      | m1_pre_topc(k2_tsep_1(sK3,sK4,X0),sK4) ) ),
    inference(resolution,[],[f64,f37])).

fof(f64,plain,(
    ! [X6,X7] :
      ( ~ m1_pre_topc(X6,sK3)
      | ~ m1_pre_topc(X7,sK3)
      | v2_struct_0(X7)
      | r1_tsep_1(X6,X7)
      | v2_struct_0(X6)
      | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6) ) ),
    inference(global_subsumption,[],[f35,f63])).

fof(f63,plain,(
    ! [X6,X7] :
      ( r1_tsep_1(X6,X7)
      | ~ m1_pre_topc(X7,sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X6,sK3)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK3)
      | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6) ) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f57,plain,(
    ! [X6,X7] :
      ( r1_tsep_1(X6,X7)
      | ~ m1_pre_topc(X7,sK3)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X6,sK3)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK3)
      | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f911,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(X10,sK4)
        | v2_struct_0(X10)
        | r1_tsep_1(sK6,X10)
        | ~ m1_pre_topc(X10,sK3) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f910,f36])).

fof(f910,plain,
    ( ! [X10] :
        ( v2_struct_0(sK4)
        | ~ m1_pre_topc(X10,sK3)
        | v2_struct_0(X10)
        | r1_tsep_1(sK6,X10)
        | ~ m1_pre_topc(X10,sK4) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f909,f37])).

fof(f909,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X10,sK3)
        | v2_struct_0(X10)
        | r1_tsep_1(sK6,X10)
        | ~ m1_pre_topc(X10,sK4) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f908,f40])).

fof(f908,plain,
    ( ! [X10] :
        ( v2_struct_0(sK6)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X10,sK3)
        | v2_struct_0(X10)
        | r1_tsep_1(sK6,X10)
        | ~ m1_pre_topc(X10,sK4) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f893,f41])).

fof(f893,plain,
    ( ! [X10] :
        ( ~ m1_pre_topc(sK6,sK3)
        | v2_struct_0(sK6)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X10,sK3)
        | v2_struct_0(X10)
        | r1_tsep_1(sK6,X10)
        | ~ m1_pre_topc(X10,sK4) )
    | ~ spl7_3 ),
    inference(resolution,[],[f350,f81])).

fof(f81,plain,
    ( r1_tsep_1(sK6,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_3
  <=> r1_tsep_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f625,plain,
    ( ~ spl7_1
    | ~ spl7_6
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f624])).

fof(f624,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_6
    | spl7_17 ),
    inference(subsumption_resolution,[],[f622,f72])).

fof(f72,plain,
    ( sP0(sK6,sK5,sK4,sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_1
  <=> sP0(sK6,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f622,plain,
    ( ~ sP0(sK6,sK5,sK4,sK3)
    | ~ spl7_6
    | spl7_17 ),
    inference(resolution,[],[f621,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_tsep_1(X1,X0)
          | r1_tsep_1(X2,X0) )
        & ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f621,plain,
    ( r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ spl7_6
    | spl7_17 ),
    inference(subsumption_resolution,[],[f620,f172])).

fof(f620,plain,
    ( r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_6
    | spl7_17 ),
    inference(subsumption_resolution,[],[f619,f288])).

fof(f619,plain,
    ( v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_6 ),
    inference(resolution,[],[f618,f131])).

fof(f618,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK4)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK6)
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f617,f36])).

fof(f617,plain,
    ( ! [X0] :
        ( v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK6)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f616,f37])).

fof(f616,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK6)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f615,f40])).

fof(f615,plain,
    ( ! [X0] :
        ( v2_struct_0(sK6)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK6)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f614,f41])).

fof(f614,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK6,sK3)
        | v2_struct_0(sK6)
        | ~ m1_pre_topc(sK4,sK3)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,sK6)
        | ~ m1_pre_topc(X0,sK4) )
    | ~ spl7_6 ),
    inference(resolution,[],[f95,f291])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f60,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X2)
      | r1_tsep_1(X2,X1) ) ),
    inference(global_subsumption,[],[f35,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK3)
      | r1_tsep_1(X2,X1) ) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,sK3)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,sK3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK3)
      | r1_tsep_1(X2,X1)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | sP1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( r1_tsep_1(sK4,sK6)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_6
  <=> r1_tsep_1(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f609,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f606,f72])).

fof(f606,plain,
    ( ~ sP0(sK6,sK5,sK4,sK3)
    | ~ spl7_5
    | spl7_17 ),
    inference(resolution,[],[f605,f31])).

fof(f605,plain,
    ( r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f604,f172])).

fof(f604,plain,
    ( r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f603,f288])).

fof(f603,plain,
    ( v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6)
    | ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f598,f233])).

fof(f598,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(X5,sK5)
        | v2_struct_0(X5)
        | r1_tsep_1(X5,sK6)
        | ~ m1_pre_topc(X5,sK3) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f597,f38])).

fof(f597,plain,
    ( ! [X5] :
        ( v2_struct_0(sK5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X5)
        | r1_tsep_1(X5,sK6)
        | ~ m1_pre_topc(X5,sK5) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f596,f39])).

fof(f596,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X5)
        | r1_tsep_1(X5,sK6)
        | ~ m1_pre_topc(X5,sK5) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f595,f40])).

fof(f595,plain,
    ( ! [X5] :
        ( v2_struct_0(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X5)
        | r1_tsep_1(X5,sK6)
        | ~ m1_pre_topc(X5,sK5) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f586,f41])).

fof(f586,plain,
    ( ! [X5] :
        ( ~ m1_pre_topc(sK6,sK3)
        | v2_struct_0(sK6)
        | ~ m1_pre_topc(sK5,sK3)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X5,sK3)
        | v2_struct_0(X5)
        | r1_tsep_1(X5,sK6)
        | ~ m1_pre_topc(X5,sK5) )
    | ~ spl7_5 ),
    inference(resolution,[],[f291,f91])).

fof(f91,plain,
    ( r1_tsep_1(sK5,sK6)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_5
  <=> r1_tsep_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f304,plain,(
    ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f302,f39])).

fof(f302,plain,
    ( ~ m1_pre_topc(sK5,sK3)
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f301,f36])).

fof(f301,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f300,f37])).

fof(f300,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f299,f38])).

fof(f299,plain,
    ( v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ spl7_17 ),
    inference(resolution,[],[f298,f68])).

fof(f298,plain,
    ( ~ sP2(sK3,sK5,sK4)
    | ~ spl7_17 ),
    inference(resolution,[],[f289,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f289,plain,
    ( v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f287])).

fof(f96,plain,
    ( spl7_5
    | spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f87,f70,f93,f89])).

fof(f87,plain,
    ( r1_tsep_1(sK4,sK6)
    | r1_tsep_1(sK5,sK6)
    | ~ spl7_1 ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,
    ( spl7_1
    | spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f44,f83,f79,f70])).

fof(f44,plain,
    ( r1_tsep_1(sK6,sK5)
    | r1_tsep_1(sK6,sK4)
    | sP0(sK6,sK5,sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f43,f74,f70])).

fof(f43,plain,
    ( ~ r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))
    | sP0(sK6,sK5,sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:39:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (25425)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (25430)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (25422)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (25426)WARNING: option uwaf not known.
% 0.20/0.47  % (25418)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.47  % (25423)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.48  % (25417)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.48  % (25426)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (25421)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (25424)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (25419)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.49  % (25427)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.49  % (25436)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.49  % (25420)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.49  % (25425)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f950,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f77,f86,f96,f304,f609,f625,f916,f949])).
% 0.20/0.49  fof(f949,plain,(
% 0.20/0.49    spl7_2 | ~spl7_4 | spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f948])).
% 0.20/0.49  fof(f948,plain,(
% 0.20/0.49    $false | (spl7_2 | ~spl7_4 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f947,f172])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~v2_struct_0(sK4)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ((((((r1_tsep_1(sK6,sK5) | r1_tsep_1(sK6,sK4)) & ~r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))) | sP0(sK6,sK5,sK4,sK3)) & ~r1_tsep_1(sK4,sK5) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f15,f25,f24,f23,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,X1,X2))) | sP0(X3,X2,X1,sK3)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,X1,X2))) | sP0(X3,X2,X1,sK3)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK3) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK4)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,sK4,X2))) | sP0(X3,X2,sK4,sK3)) & ~r1_tsep_1(sK4,X2) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) & m1_pre_topc(sK4,sK3) & ~v2_struct_0(sK4))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK4)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,sK4,X2))) | sP0(X3,X2,sK4,sK3)) & ~r1_tsep_1(sK4,X2) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK3) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(X3,sK5) | r1_tsep_1(X3,sK4)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,sK4,sK5))) | sP0(X3,sK5,sK4,sK3)) & ~r1_tsep_1(sK4,sK5) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,sK3) & ~v2_struct_0(sK5))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X3] : ((((r1_tsep_1(X3,sK5) | r1_tsep_1(X3,sK4)) & ~r1_tsep_1(X3,k2_tsep_1(sK3,sK4,sK5))) | sP0(X3,sK5,sK4,sK3)) & ~r1_tsep_1(sK4,sK5) & m1_pre_topc(X3,sK3) & ~v2_struct_0(X3)) => ((((r1_tsep_1(sK6,sK5) | r1_tsep_1(sK6,sK4)) & ~r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))) | sP0(sK6,sK5,sK4,sK3)) & ~r1_tsep_1(sK4,sK5) & m1_pre_topc(sK6,sK3) & ~v2_struct_0(sK6))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  % (25431)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(definition_folding,[],[f7,f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X3,X2,X1,X0] : (((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)),
% 0.20/0.49    inference(resolution,[],[f137,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    m1_pre_topc(sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | m1_pre_topc(k2_tsep_1(sK3,X1,sK5),sK3)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v2_struct_0(sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | v2_struct_0(sK5) | m1_pre_topc(k2_tsep_1(sK3,X1,sK5),sK3)) )),
% 0.20/0.49    inference(resolution,[],[f98,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    m1_pre_topc(sK5,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_pre_topc(X2,sK3) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | v2_struct_0(X2) | m1_pre_topc(k2_tsep_1(sK3,X3,X2),sK3)) )),
% 0.20/0.49    inference(resolution,[],[f68,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k2_tsep_1(X0,X2,X1)) & ~v2_struct_0(k2_tsep_1(X0,X2,X1))) | ~sP2(X0,X1,X2))),
% 0.20/0.49    inference(rectify,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP2(X0,X2,X1))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP2(sK3,X0,X1) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f67,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | sP2(sK3,X0,X1) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f35,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | sP2(X0,X2,X1) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(definition_folding,[],[f13,f18])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    l1_pre_topc(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f947,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (spl7_2 | ~spl7_4 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f946,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl7_2 <=> r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f946,plain,(
% 0.20/0.49    r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (~spl7_4 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f945,f288])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    ~v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | spl7_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f287])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    spl7_17 <=> v2_struct_0(k2_tsep_1(sK3,sK4,sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.49  fof(f945,plain,(
% 0.20/0.49    v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | ~spl7_4),
% 0.20/0.49    inference(resolution,[],[f932,f233])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f232,f36])).
% 0.20/0.49  fof(f232,plain,(
% 0.20/0.49    v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f231,f37])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f230,f38])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f228,f39])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK5)),
% 0.20/0.49    inference(resolution,[],[f66,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~r1_tsep_1(sK4,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X8,X9] : (r1_tsep_1(X8,X9) | ~m1_pre_topc(X9,sK3) | v2_struct_0(X9) | ~m1_pre_topc(X8,sK3) | v2_struct_0(X8) | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9)) )),
% 0.20/0.49    inference(global_subsumption,[],[f35,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X8,X9] : (r1_tsep_1(X8,X9) | ~m1_pre_topc(X9,sK3) | v2_struct_0(X9) | ~m1_pre_topc(X8,sK3) | v2_struct_0(X8) | ~l1_pre_topc(sK3) | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f58,f33])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X8,X9] : (r1_tsep_1(X8,X9) | ~m1_pre_topc(X9,sK3) | v2_struct_0(X9) | ~m1_pre_topc(X8,sK3) | v2_struct_0(X8) | ~l1_pre_topc(sK3) | m1_pre_topc(k2_tsep_1(sK3,X8,X9),X9) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f34,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    v2_pre_topc(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f932,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK5) | v2_struct_0(X0) | r1_tsep_1(sK6,X0) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f931,f38])).
% 0.20/0.49  fof(f931,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(sK6,X0) | ~m1_pre_topc(X0,sK5)) ) | ~spl7_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f930,f39])).
% 0.20/0.49  fof(f930,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(sK6,X0) | ~m1_pre_topc(X0,sK5)) ) | ~spl7_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f929,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~v2_struct_0(sK6)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f929,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(sK6,X0) | ~m1_pre_topc(X0,sK5)) ) | ~spl7_4),
% 0.20/0.49    inference(subsumption_resolution,[],[f925,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    m1_pre_topc(sK6,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f925,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(sK6,X0) | ~m1_pre_topc(X0,sK5)) ) | ~spl7_4),
% 0.20/0.49    inference(resolution,[],[f85,f350])).
% 0.20/0.49  fof(f350,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (~r1_tsep_1(X5,X4) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | r1_tsep_1(X5,X3) | ~m1_pre_topc(X3,X4)) )),
% 0.20/0.49    inference(resolution,[],[f62,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~r1_tsep_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r1_tsep_1(X1,X0) & ~r1_tsep_1(X0,X1)) | ~sP1(X0,X1))),
% 0.20/0.49    inference(rectify,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X2,X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~sP1(X2,X3))),
% 0.20/0.49    inference(nnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X2,X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~sP1(X2,X3))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (sP1(X3,X4) | ~m1_pre_topc(X5,X3) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | r1_tsep_1(X4,X5)) )),
% 0.20/0.49    inference(global_subsumption,[],[f35,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (sP1(X3,X4) | ~m1_pre_topc(X5,X3) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | ~l1_pre_topc(sK3) | r1_tsep_1(X4,X5)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f56,f33])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (sP1(X3,X4) | ~m1_pre_topc(X5,X3) | ~m1_pre_topc(X4,sK3) | v2_struct_0(X4) | ~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | ~l1_pre_topc(sK3) | r1_tsep_1(X4,X5) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f34,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | sP1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X3,X1) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | sP1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(definition_folding,[],[f11,f16])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    r1_tsep_1(sK6,sK5) | ~spl7_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl7_4 <=> r1_tsep_1(sK6,sK5)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f916,plain,(
% 0.20/0.49    spl7_2 | ~spl7_3 | spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f915])).
% 0.20/0.49  fof(f915,plain,(
% 0.20/0.49    $false | (spl7_2 | ~spl7_3 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f914,f172])).
% 0.20/0.49  fof(f914,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (spl7_2 | ~spl7_3 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f913,f76])).
% 0.20/0.49  fof(f913,plain,(
% 0.20/0.49    r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (~spl7_3 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f912,f288])).
% 0.20/0.49  fof(f912,plain,(
% 0.20/0.49    v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | ~spl7_3),
% 0.20/0.49    inference(resolution,[],[f911,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f130,f39])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ~m1_pre_topc(sK5,sK3) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f38])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    v2_struct_0(sK5) | ~m1_pre_topc(sK5,sK3) | m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK4)),
% 0.20/0.49    inference(resolution,[],[f120,f42])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tsep_1(sK4,X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | m1_pre_topc(k2_tsep_1(sK3,sK4,X0),sK4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f117,f36])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(sK4,X0) | v2_struct_0(sK4) | m1_pre_topc(k2_tsep_1(sK3,sK4,X0),sK4)) )),
% 0.20/0.49    inference(resolution,[],[f64,f37])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X6,X7] : (~m1_pre_topc(X6,sK3) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7) | r1_tsep_1(X6,X7) | v2_struct_0(X6) | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6)) )),
% 0.20/0.49    inference(global_subsumption,[],[f35,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X6,X7] : (r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7) | ~m1_pre_topc(X6,sK3) | v2_struct_0(X6) | ~l1_pre_topc(sK3) | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f57,f33])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X6,X7] : (r1_tsep_1(X6,X7) | ~m1_pre_topc(X7,sK3) | v2_struct_0(X7) | ~m1_pre_topc(X6,sK3) | v2_struct_0(X6) | ~l1_pre_topc(sK3) | m1_pre_topc(k2_tsep_1(sK3,X6,X7),X6) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f34,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f911,plain,(
% 0.20/0.49    ( ! [X10] : (~m1_pre_topc(X10,sK4) | v2_struct_0(X10) | r1_tsep_1(sK6,X10) | ~m1_pre_topc(X10,sK3)) ) | ~spl7_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f910,f36])).
% 0.20/0.49  fof(f910,plain,(
% 0.20/0.49    ( ! [X10] : (v2_struct_0(sK4) | ~m1_pre_topc(X10,sK3) | v2_struct_0(X10) | r1_tsep_1(sK6,X10) | ~m1_pre_topc(X10,sK4)) ) | ~spl7_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f909,f37])).
% 0.20/0.49  fof(f909,plain,(
% 0.20/0.49    ( ! [X10] : (~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X10,sK3) | v2_struct_0(X10) | r1_tsep_1(sK6,X10) | ~m1_pre_topc(X10,sK4)) ) | ~spl7_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f908,f40])).
% 0.20/0.49  fof(f908,plain,(
% 0.20/0.49    ( ! [X10] : (v2_struct_0(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X10,sK3) | v2_struct_0(X10) | r1_tsep_1(sK6,X10) | ~m1_pre_topc(X10,sK4)) ) | ~spl7_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f893,f41])).
% 0.20/0.49  fof(f893,plain,(
% 0.20/0.49    ( ! [X10] : (~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X10,sK3) | v2_struct_0(X10) | r1_tsep_1(sK6,X10) | ~m1_pre_topc(X10,sK4)) ) | ~spl7_3),
% 0.20/0.49    inference(resolution,[],[f350,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    r1_tsep_1(sK6,sK4) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl7_3 <=> r1_tsep_1(sK6,sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f625,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_6 | spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f624])).
% 0.20/0.49  fof(f624,plain,(
% 0.20/0.49    $false | (~spl7_1 | ~spl7_6 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f622,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    sP0(sK6,sK5,sK4,sK3) | ~spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl7_1 <=> sP0(sK6,sK5,sK4,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f622,plain,(
% 0.20/0.49    ~sP0(sK6,sK5,sK4,sK3) | (~spl7_6 | spl7_17)),
% 0.20/0.49    inference(resolution,[],[f621,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (((r1_tsep_1(X1,X0) | r1_tsep_1(X2,X0)) & ~r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)) | ~sP0(X0,X1,X2,X3))),
% 0.20/0.49    inference(rectify,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X3,X2,X1,X0] : (((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)) | ~sP0(X3,X2,X1,X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f621,plain,(
% 0.20/0.49    r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | (~spl7_6 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f620,f172])).
% 0.20/0.49  fof(f620,plain,(
% 0.20/0.49    r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (~spl7_6 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f619,f288])).
% 0.20/0.49  fof(f619,plain,(
% 0.20/0.49    v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | ~spl7_6),
% 0.20/0.49    inference(resolution,[],[f618,f131])).
% 0.20/0.49  fof(f618,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK4) | v2_struct_0(X0) | r1_tsep_1(X0,sK6) | ~m1_pre_topc(X0,sK3)) ) | ~spl7_6),
% 0.20/0.49    inference(subsumption_resolution,[],[f617,f36])).
% 0.20/0.49  fof(f617,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK4) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,sK6) | ~m1_pre_topc(X0,sK4)) ) | ~spl7_6),
% 0.20/0.49    inference(subsumption_resolution,[],[f616,f37])).
% 0.20/0.49  fof(f616,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,sK6) | ~m1_pre_topc(X0,sK4)) ) | ~spl7_6),
% 0.20/0.49    inference(subsumption_resolution,[],[f615,f40])).
% 0.20/0.49  fof(f615,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,sK6) | ~m1_pre_topc(X0,sK4)) ) | ~spl7_6),
% 0.20/0.49    inference(subsumption_resolution,[],[f614,f41])).
% 0.20/0.49  fof(f614,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,sK6) | ~m1_pre_topc(X0,sK4)) ) | ~spl7_6),
% 0.20/0.49    inference(resolution,[],[f95,f291])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | r1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f60,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~r1_tsep_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | r1_tsep_1(X2,X1)) )),
% 0.20/0.49    inference(global_subsumption,[],[f35,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | r1_tsep_1(X2,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f55,f33])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK3) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | r1_tsep_1(X2,X1) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f34,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | sP1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X1,X3) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    r1_tsep_1(sK4,sK6) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl7_6 <=> r1_tsep_1(sK4,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f609,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_5 | spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f608])).
% 0.20/0.49  fof(f608,plain,(
% 0.20/0.49    $false | (~spl7_1 | ~spl7_5 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f606,f72])).
% 0.20/0.49  fof(f606,plain,(
% 0.20/0.49    ~sP0(sK6,sK5,sK4,sK3) | (~spl7_5 | spl7_17)),
% 0.20/0.49    inference(resolution,[],[f605,f31])).
% 0.20/0.49  fof(f605,plain,(
% 0.20/0.49    r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | (~spl7_5 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f604,f172])).
% 0.20/0.49  fof(f604,plain,(
% 0.20/0.49    r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | (~spl7_5 | spl7_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f603,f288])).
% 0.20/0.49  fof(f603,plain,(
% 0.20/0.49    v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | r1_tsep_1(k2_tsep_1(sK3,sK4,sK5),sK6) | ~m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f598,f233])).
% 0.20/0.49  fof(f598,plain,(
% 0.20/0.49    ( ! [X5] : (~m1_pre_topc(X5,sK5) | v2_struct_0(X5) | r1_tsep_1(X5,sK6) | ~m1_pre_topc(X5,sK3)) ) | ~spl7_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f597,f38])).
% 0.20/0.49  fof(f597,plain,(
% 0.20/0.49    ( ! [X5] : (v2_struct_0(sK5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | r1_tsep_1(X5,sK6) | ~m1_pre_topc(X5,sK5)) ) | ~spl7_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f596,f39])).
% 0.20/0.49  fof(f596,plain,(
% 0.20/0.49    ( ! [X5] : (~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | r1_tsep_1(X5,sK6) | ~m1_pre_topc(X5,sK5)) ) | ~spl7_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f595,f40])).
% 0.20/0.49  fof(f595,plain,(
% 0.20/0.49    ( ! [X5] : (v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | r1_tsep_1(X5,sK6) | ~m1_pre_topc(X5,sK5)) ) | ~spl7_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f586,f41])).
% 0.20/0.49  fof(f586,plain,(
% 0.20/0.49    ( ! [X5] : (~m1_pre_topc(sK6,sK3) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK3) | v2_struct_0(sK5) | ~m1_pre_topc(X5,sK3) | v2_struct_0(X5) | r1_tsep_1(X5,sK6) | ~m1_pre_topc(X5,sK5)) ) | ~spl7_5),
% 0.20/0.49    inference(resolution,[],[f291,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    r1_tsep_1(sK5,sK6) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl7_5 <=> r1_tsep_1(sK5,sK6)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f304,plain,(
% 0.20/0.49    ~spl7_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f303])).
% 0.20/0.49  fof(f303,plain,(
% 0.20/0.49    $false | ~spl7_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f302,f39])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    ~m1_pre_topc(sK5,sK3) | ~spl7_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f301,f36])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | ~spl7_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f300,f37])).
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | ~spl7_17),
% 0.20/0.49    inference(subsumption_resolution,[],[f299,f38])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK4) | ~m1_pre_topc(sK5,sK3) | ~spl7_17),
% 0.20/0.49    inference(resolution,[],[f298,f68])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    ~sP2(sK3,sK5,sK4) | ~spl7_17),
% 0.20/0.49    inference(resolution,[],[f289,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X2,X1)) | ~sP2(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) | ~spl7_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f287])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl7_5 | spl7_6 | ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f87,f70,f93,f89])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    r1_tsep_1(sK4,sK6) | r1_tsep_1(sK5,sK6) | ~spl7_1),
% 0.20/0.49    inference(resolution,[],[f72,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0) | r1_tsep_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl7_1 | spl7_3 | spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f83,f79,f70])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    r1_tsep_1(sK6,sK5) | r1_tsep_1(sK6,sK4) | sP0(sK6,sK5,sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f74,f70])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ~r1_tsep_1(sK6,k2_tsep_1(sK3,sK4,sK5)) | sP0(sK6,sK5,sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (25425)------------------------------
% 0.20/0.49  % (25425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25425)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (25425)Memory used [KB]: 10362
% 0.20/0.49  % (25425)Time elapsed: 0.093 s
% 0.20/0.49  % (25425)------------------------------
% 0.20/0.49  % (25425)------------------------------
% 0.20/0.50  % (25416)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (25415)Success in time 0.148 s
%------------------------------------------------------------------------------
