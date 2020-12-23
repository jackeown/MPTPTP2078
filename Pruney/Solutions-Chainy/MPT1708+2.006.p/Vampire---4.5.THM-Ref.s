%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 419 expanded)
%              Number of leaves         :   40 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  843 (3395 expanded)
%              Number of equality atoms :  131 ( 578 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f121,f149,f152,f154,f156,f166,f168,f170,f196,f202,f225,f235,f237,f243,f248,f280,f295,f303,f305])).

% (15055)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f305,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f290,f97])).

fof(f97,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f290,plain,
    ( ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl7_25
  <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f303,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f300,f50])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ! [X4] :
          ( sK5 != X4
          | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
      | ! [X5] :
          ( sK5 != X5
          | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
    & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))
    & ~ r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ! [X4] :
                          ( X3 != X4
                          | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                      | ! [X5] :
                          ( X3 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                    & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
                & ~ r1_tsep_1(X1,X2)
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
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  | ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2))) )
            & ~ r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                | ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
              & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2))) )
          & ~ r1_tsep_1(sK3,X2)
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              | ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
            & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2))) )
        & ~ r1_tsep_1(sK3,X2)
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
            | ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
          & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) )
      & ~ r1_tsep_1(sK3,sK4)
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

% (15045)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f36,plain,
    ( ? [X3] :
        ( ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
          | ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
        & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) )
   => ( ( ! [X4] :
            ( sK5 != X4
            | ~ m1_subset_1(X4,u1_struct_0(sK4)) )
        | ! [X5] :
            ( sK5 != X5
            | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) )
      & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,negated_conjecture,(
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
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f300,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_26 ),
    inference(resolution,[],[f299,f54])).

fof(f54,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_26 ),
    inference(resolution,[],[f294,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f294,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl7_26
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f295,plain,
    ( ~ spl7_25
    | ~ spl7_26
    | spl7_9
    | ~ spl7_10
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f284,f278,f119,f109,f146,f142,f292,f288])).

fof(f142,plain,
    ( spl7_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f146,plain,
    ( spl7_10
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f109,plain,
    ( spl7_2
  <=> m1_subset_1(sK5,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f119,plain,
    ( spl7_4
  <=> ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f278,plain,
    ( spl7_24
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f284,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f282,f111])).

fof(f111,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f282,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) )
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(resolution,[],[f281,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK5,u1_struct_0(X0)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f281,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))
        | ~ m1_pre_topc(X0,sK2) )
    | ~ spl7_24 ),
    inference(resolution,[],[f279,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f29,f31,f30])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(f279,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | ~ m1_pre_topc(X0,sK2)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( ~ spl7_6
    | ~ spl7_19
    | spl7_24
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f276,f199,f278,f232,f130])).

fof(f130,plain,
    ( spl7_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f232,plain,
    ( spl7_19
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f199,plain,
    ( spl7_14
  <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f276,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
        | ~ l1_pre_topc(sK2)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6)
        | ~ sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f275,f49])).

fof(f49,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f275,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7)
        | ~ sP1(X7,X6,X5,X4,X3,X2,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(resolution,[],[f257,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f43])).

% (15037)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP0(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ~ sP0(X7,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(u1_struct_0(X0),k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
        | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f206,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f206,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2)
        | ~ r2_hidden(X2,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_14 ),
    inference(superposition,[],[f67,f201])).

fof(f201,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f248,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f245,f50])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_20 ),
    inference(resolution,[],[f244,f52])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_20 ),
    inference(resolution,[],[f242,f58])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl7_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f243,plain,
    ( spl7_1
    | ~ spl7_20
    | spl7_7
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f238,f222,f119,f134,f240,f105])).

fof(f105,plain,
    ( spl7_1
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f134,plain,
    ( spl7_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f222,plain,
    ( spl7_18
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f238,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_4
    | ~ spl7_18 ),
    inference(resolution,[],[f224,f120])).

fof(f224,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f222])).

fof(f237,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | spl7_19 ),
    inference(avatar_split_clause,[],[f236,f232,f146,f142,f138,f134,f130,f126])).

fof(f126,plain,
    ( spl7_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f138,plain,
    ( spl7_8
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f236,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_19 ),
    inference(resolution,[],[f234,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

% (15061)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (15038)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (15054)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (15035)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (15045)Refutation not found, incomplete strategy% (15045)------------------------------
% (15045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15045)Termination reason: Refutation not found, incomplete strategy

% (15045)Memory used [KB]: 10746
% (15045)Time elapsed: 0.121 s
% (15045)------------------------------
% (15045)------------------------------
% (15057)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (15062)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (15043)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (15044)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (15049)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f234,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( ~ spl7_19
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f230,f219,f138,f130,f232])).

fof(f219,plain,
    ( spl7_17
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f230,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl7_17 ),
    inference(resolution,[],[f220,f49])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f219])).

fof(f225,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f217,f199,f222,f219])).

fof(f217,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f205,f62])).

fof(f205,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3))
    | ~ spl7_14 ),
    inference(superposition,[],[f93,f201])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f88])).

% (15058)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

% (15053)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f202,plain,
    ( spl7_14
    | spl7_3
    | ~ spl7_8
    | ~ spl7_6
    | spl7_5
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f197,f194,f126,f130,f138,f115,f199])).

fof(f115,plain,
    ( spl7_3
  <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f194,plain,
    ( spl7_13
  <=> ! [X0] :
        ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK4,X0)
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f197,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
    | ~ spl7_13 ),
    inference(resolution,[],[f195,f54])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(k2_tsep_1(X0,sK3,sK4))
        | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f196,plain,
    ( spl7_7
    | spl7_9
    | spl7_13 ),
    inference(avatar_split_clause,[],[f192,f194,f142,f134])).

fof(f192,plain,(
    ! [X0] :
      ( v2_struct_0(k2_tsep_1(X0,sK3,sK4))
      | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))
      | ~ m1_pre_topc(sK4,X0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK3,X0)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f191,f55])).

fof(f55,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f189,f71])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f96,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2)))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f90])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f170,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl7_9 ),
    inference(resolution,[],[f144,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f144,plain,
    ( v2_struct_0(sK4)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f168,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl7_7 ),
    inference(resolution,[],[f136,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f136,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f166,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl7_5 ),
    inference(resolution,[],[f128,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f156,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f148,f54])).

fof(f148,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f154,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f140,f52])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f152,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl7_6 ),
    inference(resolution,[],[f132,f50])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f149,plain,
    ( spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_10
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f124,f115,f146,f142,f138,f134,f130,f126])).

fof(f124,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f117])).

fof(f117,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f113,f119,f115])).

fof(f113,plain,(
    ! [X0] :
      ( m1_subset_1(sK5,u1_struct_0(X0))
      | ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)
      | v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f59,f56])).

fof(f56,plain,(
    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f112,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f95,f109,f105])).

fof(f95,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X5] :
      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X5] :
      ( sK5 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK4))
      | sK5 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (15034)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (15060)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (15040)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (15050)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (15036)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (15047)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (15059)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (15056)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (15041)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (15063)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (15039)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (15048)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (15046)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (15051)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (15052)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.56  % (15042)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (15046)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f306,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f112,f121,f149,f152,f154,f156,f166,f168,f170,f196,f202,f225,f235,f237,f243,f248,f280,f295,f303,f305])).
% 0.20/0.56  % (15055)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  fof(f305,plain,(
% 0.20/0.56    spl7_25),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f304])).
% 0.20/0.56  fof(f304,plain,(
% 0.20/0.56    $false | spl7_25),
% 0.20/0.56    inference(resolution,[],[f290,f97])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.56    inference(equality_resolution,[],[f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 0.20/0.56    inference(rectify,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.56    inference(flattening,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.56    inference(nnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X7,X5,X4,X3,X2,X1,X0] : (sP0(X7,X5,X4,X3,X2,X1,X0) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f290,plain,(
% 0.20/0.56    ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | spl7_25),
% 0.20/0.56    inference(avatar_component_clause,[],[f288])).
% 0.20/0.56  fof(f288,plain,(
% 0.20/0.56    spl7_25 <=> sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.56  fof(f303,plain,(
% 0.20/0.56    spl7_26),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f301])).
% 0.20/0.56  fof(f301,plain,(
% 0.20/0.56    $false | spl7_26),
% 0.20/0.56    inference(resolution,[],[f300,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    l1_pre_topc(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ((((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36,f35,f34,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,X2)))) & ~r1_tsep_1(sK3,X2) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) & ~r1_tsep_1(sK3,sK4) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  % (15045)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))) => ((! [X4] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4))) | ! [X5] : (sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3)))) & m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 0.20/0.56    inference(rectify,[],[f15])).
% 0.20/0.56  fof(f15,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f14])).
% 0.20/0.56  fof(f14,conjecture,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 0.20/0.56  fof(f300,plain,(
% 0.20/0.56    ~l1_pre_topc(sK2) | spl7_26),
% 0.20/0.56    inference(resolution,[],[f299,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    m1_pre_topc(sK4,sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f299,plain,(
% 0.20/0.56    ( ! [X0] : (~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) ) | spl7_26),
% 0.20/0.56    inference(resolution,[],[f294,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.56  fof(f294,plain,(
% 0.20/0.56    ~l1_pre_topc(sK4) | spl7_26),
% 0.20/0.56    inference(avatar_component_clause,[],[f292])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    spl7_26 <=> l1_pre_topc(sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.56  fof(f295,plain,(
% 0.20/0.56    ~spl7_25 | ~spl7_26 | spl7_9 | ~spl7_10 | spl7_2 | ~spl7_4 | ~spl7_24),
% 0.20/0.56    inference(avatar_split_clause,[],[f284,f278,f119,f109,f146,f142,f292,f288])).
% 0.20/0.56  fof(f142,plain,(
% 0.20/0.56    spl7_9 <=> v2_struct_0(sK4)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.56  fof(f146,plain,(
% 0.20/0.56    spl7_10 <=> m1_pre_topc(sK4,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    spl7_2 <=> m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    spl7_4 <=> ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.56  fof(f278,plain,(
% 0.20/0.56    spl7_24 <=> ! [X1,X3,X5,X0,X2,X4,X6] : (~m1_pre_topc(X0,sK2) | ~sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | ~sP0(u1_struct_0(sK4),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | (spl7_2 | ~spl7_4 | ~spl7_24)),
% 0.20/0.56    inference(resolution,[],[f282,f111])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ~m1_subset_1(sK5,u1_struct_0(sK4)) | spl7_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f109])).
% 0.20/0.56  fof(f282,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3))) ) | (~spl7_4 | ~spl7_24)),
% 0.20/0.56    inference(resolution,[],[f281,f120])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    ( ! [X0] : (~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK5,u1_struct_0(X0))) ) | ~spl7_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f119])).
% 0.20/0.56  fof(f281,plain,(
% 0.20/0.56    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),u1_struct_0(sK4),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3)) | ~m1_pre_topc(X0,sK2)) ) | ~spl7_24),
% 0.20/0.56    inference(resolution,[],[f279,f103])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.56    inference(equality_resolution,[],[f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.20/0.56    inference(cnf_transformation,[],[f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) & (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 0.20/0.56    inference(nnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP1(X0,X1,X2,X3,X4,X5,X6))),
% 0.20/0.56    inference(definition_folding,[],[f29,f31,f30])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : (sP1(X0,X1,X2,X3,X4,X5,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).
% 0.20/0.56  fof(f279,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(X0,sK2) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_24),
% 0.20/0.56    inference(avatar_component_clause,[],[f278])).
% 0.20/0.56  fof(f280,plain,(
% 0.20/0.56    ~spl7_6 | ~spl7_19 | spl7_24 | ~spl7_14),
% 0.20/0.56    inference(avatar_split_clause,[],[f276,f199,f278,f232,f130])).
% 0.20/0.56  fof(f130,plain,(
% 0.20/0.56    spl7_6 <=> l1_pre_topc(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    spl7_19 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    spl7_14 <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.56  fof(f276,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~l1_pre_topc(sK2) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X1,X2,X3,X4,X5,X6) | ~sP1(X6,X5,X4,X3,X2,X1,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.20/0.56    inference(resolution,[],[f275,f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    v2_pre_topc(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f275,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~v2_pre_topc(X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~sP0(u1_struct_0(X0),X2,X3,X4,X5,X6,X7) | ~sP1(X7,X6,X5,X4,X3,X2,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.20/0.56    inference(resolution,[],[f257,f75])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f43])).
% 0.20/0.56  % (15037)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6))) => ((~sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK6(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK6(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 0.20/0.56    inference(rectify,[],[f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | ~sP0(X7,X5,X4,X3,X2,X1,X0)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 0.20/0.56    inference(nnf_transformation,[],[f31])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(u1_struct_0(X0),k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) ) | ~spl7_14),
% 0.20/0.56    inference(resolution,[],[f206,f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.56  fof(f206,plain,(
% 0.20/0.56    ( ! [X2] : (r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),X2) | ~r2_hidden(X2,k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_14),
% 0.20/0.56    inference(superposition,[],[f67,f201])).
% 0.20/0.56  fof(f201,plain,(
% 0.20/0.56    u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_14),
% 0.20/0.56    inference(avatar_component_clause,[],[f199])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.56  fof(f248,plain,(
% 0.20/0.56    spl7_20),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    $false | spl7_20),
% 0.20/0.56    inference(resolution,[],[f245,f50])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    ~l1_pre_topc(sK2) | spl7_20),
% 0.20/0.56    inference(resolution,[],[f244,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    m1_pre_topc(sK3,sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f244,plain,(
% 0.20/0.56    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl7_20),
% 0.20/0.56    inference(resolution,[],[f242,f58])).
% 0.20/0.56  fof(f242,plain,(
% 0.20/0.56    ~l1_pre_topc(sK3) | spl7_20),
% 0.20/0.56    inference(avatar_component_clause,[],[f240])).
% 0.20/0.56  fof(f240,plain,(
% 0.20/0.56    spl7_20 <=> l1_pre_topc(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.56  fof(f243,plain,(
% 0.20/0.56    spl7_1 | ~spl7_20 | spl7_7 | ~spl7_4 | ~spl7_18),
% 0.20/0.56    inference(avatar_split_clause,[],[f238,f222,f119,f134,f240,f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    spl7_1 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    spl7_7 <=> v2_struct_0(sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.56  fof(f222,plain,(
% 0.20/0.56    spl7_18 <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_4 | ~spl7_18)),
% 0.20/0.56    inference(resolution,[],[f224,f120])).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~spl7_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f222])).
% 0.20/0.56  fof(f237,plain,(
% 0.20/0.56    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | spl7_19),
% 0.20/0.56    inference(avatar_split_clause,[],[f236,f232,f146,f142,f138,f134,f130,f126])).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    spl7_5 <=> v2_struct_0(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    spl7_8 <=> m1_pre_topc(sK3,sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | spl7_19),
% 0.20/0.56    inference(resolution,[],[f234,f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f27])).
% 0.20/0.56  % (15061)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (15038)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (15054)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (15035)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.57  % (15045)Refutation not found, incomplete strategy% (15045)------------------------------
% 0.20/0.57  % (15045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (15045)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (15045)Memory used [KB]: 10746
% 0.20/0.57  % (15045)Time elapsed: 0.121 s
% 0.20/0.57  % (15045)------------------------------
% 0.20/0.57  % (15045)------------------------------
% 0.20/0.57  % (15057)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (15062)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (15043)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % (15044)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.57  % (15049)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.20/0.58  fof(f234,plain,(
% 0.20/0.58    ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | spl7_19),
% 0.20/0.58    inference(avatar_component_clause,[],[f232])).
% 0.20/0.58  fof(f235,plain,(
% 0.20/0.58    ~spl7_19 | ~spl7_6 | ~spl7_8 | ~spl7_17),
% 0.20/0.58    inference(avatar_split_clause,[],[f230,f219,f138,f130,f232])).
% 0.20/0.58  fof(f219,plain,(
% 0.20/0.58    spl7_17 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.58  fof(f230,plain,(
% 0.20/0.58    ~m1_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) | ~spl7_17),
% 0.20/0.58    inference(resolution,[],[f220,f49])).
% 0.20/0.58  fof(f220,plain,(
% 0.20/0.58    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0)) ) | ~spl7_17),
% 0.20/0.58    inference(avatar_component_clause,[],[f219])).
% 0.20/0.58  fof(f225,plain,(
% 0.20/0.58    spl7_17 | spl7_18 | ~spl7_14),
% 0.20/0.58    inference(avatar_split_clause,[],[f217,f199,f222,f219])).
% 0.20/0.58  fof(f217,plain,(
% 0.20/0.58    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl7_14),
% 0.20/0.58    inference(resolution,[],[f205,f62])).
% 0.20/0.58  fof(f205,plain,(
% 0.20/0.58    r1_tarski(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK3)) | ~spl7_14),
% 0.20/0.58    inference(superposition,[],[f93,f201])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f64,f90])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f65,f89])).
% 0.20/0.58  fof(f89,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f66,f88])).
% 0.20/0.58  % (15058)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f68,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f72,f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.58  fof(f72,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  % (15053)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.58  fof(f202,plain,(
% 0.20/0.58    spl7_14 | spl7_3 | ~spl7_8 | ~spl7_6 | spl7_5 | ~spl7_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f197,f194,f126,f130,f138,f115,f199])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    spl7_3 <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.58  fof(f194,plain,(
% 0.20/0.58    spl7_13 <=> ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK4,X0) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.58  fof(f197,plain,(
% 0.20/0.58    v2_struct_0(sK2) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~spl7_13),
% 0.20/0.58    inference(resolution,[],[f195,f54])).
% 0.20/0.58  fof(f195,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_pre_topc(sK4,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4)))) ) | ~spl7_13),
% 0.20/0.58    inference(avatar_component_clause,[],[f194])).
% 0.20/0.58  fof(f196,plain,(
% 0.20/0.58    spl7_7 | spl7_9 | spl7_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f192,f194,f142,f134])).
% 0.20/0.58  fof(f192,plain,(
% 0.20/0.58    ( ! [X0] : (v2_struct_0(k2_tsep_1(X0,sK3,sK4)) | u1_struct_0(k2_tsep_1(X0,sK3,sK4)) = k1_setfam_1(k4_enumset1(u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK3),u1_struct_0(sK4))) | ~m1_pre_topc(sK4,X0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f191,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ~r1_tsep_1(sK3,sK4)),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f191,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f190])).
% 0.20/0.58  fof(f190,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f189,f71])).
% 0.20/0.58  fof(f189,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.58  fof(f188,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f96,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | u1_struct_0(k2_tsep_1(X0,X1,X2)) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k1_setfam_1(k4_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2))) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(definition_unfolding,[],[f60,f90])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.20/0.58  fof(f170,plain,(
% 0.20/0.58    ~spl7_9),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.58  fof(f169,plain,(
% 0.20/0.58    $false | ~spl7_9),
% 0.20/0.58    inference(resolution,[],[f144,f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ~v2_struct_0(sK4)),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    v2_struct_0(sK4) | ~spl7_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f142])).
% 0.20/0.58  fof(f168,plain,(
% 0.20/0.58    ~spl7_7),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f167])).
% 0.20/0.58  fof(f167,plain,(
% 0.20/0.58    $false | ~spl7_7),
% 0.20/0.58    inference(resolution,[],[f136,f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ~v2_struct_0(sK3)),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    v2_struct_0(sK3) | ~spl7_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f134])).
% 0.20/0.58  fof(f166,plain,(
% 0.20/0.58    ~spl7_5),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.58  fof(f165,plain,(
% 0.20/0.58    $false | ~spl7_5),
% 0.20/0.58    inference(resolution,[],[f128,f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ~v2_struct_0(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    v2_struct_0(sK2) | ~spl7_5),
% 0.20/0.58    inference(avatar_component_clause,[],[f126])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    spl7_10),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f155])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    $false | spl7_10),
% 0.20/0.58    inference(resolution,[],[f148,f54])).
% 0.20/0.58  fof(f148,plain,(
% 0.20/0.58    ~m1_pre_topc(sK4,sK2) | spl7_10),
% 0.20/0.58    inference(avatar_component_clause,[],[f146])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    spl7_8),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.58  fof(f153,plain,(
% 0.20/0.58    $false | spl7_8),
% 0.20/0.58    inference(resolution,[],[f140,f52])).
% 0.20/0.58  fof(f140,plain,(
% 0.20/0.58    ~m1_pre_topc(sK3,sK2) | spl7_8),
% 0.20/0.58    inference(avatar_component_clause,[],[f138])).
% 0.20/0.58  fof(f152,plain,(
% 0.20/0.58    spl7_6),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f150])).
% 0.20/0.58  fof(f150,plain,(
% 0.20/0.58    $false | spl7_6),
% 0.20/0.58    inference(resolution,[],[f132,f50])).
% 0.20/0.58  fof(f132,plain,(
% 0.20/0.58    ~l1_pre_topc(sK2) | spl7_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f130])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    spl7_5 | ~spl7_6 | spl7_7 | ~spl7_8 | spl7_9 | ~spl7_10 | ~spl7_3),
% 0.20/0.58    inference(avatar_split_clause,[],[f124,f115,f146,f142,f138,f134,f130,f126])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | v2_struct_0(sK2) | ~spl7_3),
% 0.20/0.58    inference(resolution,[],[f69,f117])).
% 0.20/0.58  fof(f117,plain,(
% 0.20/0.58    v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~spl7_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f115])).
% 0.20/0.58  fof(f69,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f121,plain,(
% 0.20/0.58    spl7_3 | spl7_4),
% 0.20/0.58    inference(avatar_split_clause,[],[f113,f119,f115])).
% 0.20/0.58  fof(f113,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(sK5,u1_struct_0(X0)) | ~m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),X0) | v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f59,f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    m1_subset_1(sK5,u1_struct_0(k2_tsep_1(sK2,sK3,sK4)))),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f20])).
% 0.20/0.58  fof(f20,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ~spl7_1 | ~spl7_2),
% 0.20/0.58    inference(avatar_split_clause,[],[f95,f109,f105])).
% 0.20/0.58  fof(f95,plain,(
% 0.20/0.58    ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.58    inference(equality_resolution,[],[f94])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X5] : (~m1_subset_1(sK5,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 0.20/0.58    inference(equality_resolution,[],[f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X4,X5] : (sK5 != X4 | ~m1_subset_1(X4,u1_struct_0(sK4)) | sK5 != X5 | ~m1_subset_1(X5,u1_struct_0(sK3))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  % SZS output end Proof for theBenchmark
% 0.20/0.58  % (15046)------------------------------
% 0.20/0.58  % (15046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (15046)Termination reason: Refutation
% 0.20/0.58  
% 0.20/0.58  % (15046)Memory used [KB]: 6524
% 0.20/0.58  % (15046)Time elapsed: 0.133 s
% 0.20/0.58  % (15046)------------------------------
% 0.20/0.58  % (15046)------------------------------
% 0.20/0.58  % (15033)Success in time 0.217 s
%------------------------------------------------------------------------------
