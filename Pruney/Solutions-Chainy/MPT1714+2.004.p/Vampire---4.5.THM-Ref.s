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
% DateTime   : Thu Dec  3 13:17:53 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 608 expanded)
%              Number of leaves         :   21 ( 219 expanded)
%              Depth                    :   25
%              Number of atoms          :  501 (4978 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f95,f200,f225,f1118,f1259,f1263])).

fof(f1263,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f1262])).

fof(f1262,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f84,f1261])).

fof(f1261,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f1260,f134])).

fof(f134,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f102,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f102,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f98,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f47])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1260,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f162,f154])).

fof(f154,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f162,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f81,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_1
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f84,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_2
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1259,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1258])).

fof(f1258,plain,
    ( $false
    | ~ spl6_2
    | spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1257,f154])).

fof(f1257,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1256,f109])).

fof(f109,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f101,f54])).

fof(f101,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f97,f45])).

fof(f97,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1256,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1255,f90])).

fof(f90,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1255,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(resolution,[],[f1120,f63])).

fof(f1120,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1119,f154])).

fof(f1119,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1113,f109])).

fof(f1113,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(resolution,[],[f1040,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f1040,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_14 ),
    inference(superposition,[],[f888,f228])).

fof(f228,plain,
    ( u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_14 ),
    inference(resolution,[],[f199,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f199,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_14
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f888,plain,
    ( ! [X0] : r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2)))
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f885])).

fof(f885,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2)))
        | r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f622,f106])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(X3,k3_xboole_0(X4,X5)),X5)
      | r1_xboole_0(X3,k3_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f76,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f622,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(sK2))
        | r1_xboole_0(u1_struct_0(sK3),X0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f210,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f160,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f160,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f159,f154])).

fof(f159,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f137,f134])).

fof(f137,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f52,f85])).

fof(f85,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1118,plain,
    ( ~ spl6_2
    | spl6_4
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | ~ spl6_2
    | spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1116,f154])).

fof(f1116,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1115,f109])).

fof(f1115,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ spl6_2
    | spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1113,f94])).

fof(f94,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_4
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f225,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f223,f46])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f222,f45])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f221,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f221,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl6_13 ),
    inference(resolution,[],[f195,f47])).

fof(f195,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK2,X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_13
  <=> ! [X3] :
        ( ~ m1_pre_topc(sK2,X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f200,plain,
    ( spl6_13
    | spl6_14 ),
    inference(avatar_split_clause,[],[f168,f197,f194])).

fof(f168,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
      | ~ m1_pre_topc(sK2,X3)
      | ~ m1_pre_topc(sK1,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3) ) ),
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f95,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f50,f92,f88])).

fof(f50,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f51,f83,f79])).

fof(f51,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 14:06:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (19803)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.51  % (19804)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (19809)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.52  % (19795)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (19796)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (19793)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (19804)Refutation not found, incomplete strategy% (19804)------------------------------
% 0.23/0.52  % (19804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (19804)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (19804)Memory used [KB]: 6140
% 0.23/0.52  % (19804)Time elapsed: 0.094 s
% 0.23/0.52  % (19804)------------------------------
% 0.23/0.52  % (19804)------------------------------
% 0.23/0.53  % (19814)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (19794)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (19812)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (19801)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.53  % (19806)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.30/0.54  % (19792)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (19811)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.30/0.54  % (19798)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.30/0.54  % (19810)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.30/0.55  % (19797)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.30/0.55  % (19808)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.55  % (19791)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.30/0.55  % (19791)Refutation not found, incomplete strategy% (19791)------------------------------
% 1.30/0.55  % (19791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (19791)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (19791)Memory used [KB]: 10618
% 1.30/0.55  % (19791)Time elapsed: 0.102 s
% 1.30/0.55  % (19791)------------------------------
% 1.30/0.55  % (19791)------------------------------
% 1.30/0.55  % (19797)Refutation not found, incomplete strategy% (19797)------------------------------
% 1.30/0.55  % (19797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (19813)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.48/0.56  % (19797)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (19797)Memory used [KB]: 10746
% 1.48/0.56  % (19797)Time elapsed: 0.095 s
% 1.48/0.56  % (19797)------------------------------
% 1.48/0.56  % (19797)------------------------------
% 1.48/0.56  % (19805)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.48/0.56  % (19802)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.48/0.56  % (19800)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.48/0.57  % (19798)Refutation not found, incomplete strategy% (19798)------------------------------
% 1.48/0.57  % (19798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (19798)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (19798)Memory used [KB]: 1663
% 1.48/0.57  % (19798)Time elapsed: 0.083 s
% 1.48/0.57  % (19798)------------------------------
% 1.48/0.57  % (19798)------------------------------
% 1.48/0.57  % (19799)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.48/0.57  % (19816)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.48/0.58  % (19807)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.48/0.59  % (19801)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.59  % SZS output start Proof for theBenchmark
% 1.48/0.59  fof(f1264,plain,(
% 1.48/0.59    $false),
% 1.48/0.59    inference(avatar_sat_refutation,[],[f86,f95,f200,f225,f1118,f1259,f1263])).
% 1.48/0.59  fof(f1263,plain,(
% 1.48/0.59    ~spl6_1 | spl6_2),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f1262])).
% 1.48/0.59  fof(f1262,plain,(
% 1.48/0.59    $false | (~spl6_1 | spl6_2)),
% 1.48/0.59    inference(subsumption_resolution,[],[f84,f1261])).
% 1.48/0.59  fof(f1261,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK2) | ~spl6_1),
% 1.48/0.59    inference(subsumption_resolution,[],[f1260,f134])).
% 1.48/0.59  fof(f134,plain,(
% 1.48/0.59    l1_struct_0(sK2)),
% 1.48/0.59    inference(resolution,[],[f102,f54])).
% 1.48/0.59  fof(f54,plain,(
% 1.48/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f18])).
% 1.48/0.59  fof(f18,plain,(
% 1.48/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f6])).
% 1.48/0.59  fof(f6,axiom,(
% 1.48/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.48/0.59  fof(f102,plain,(
% 1.48/0.59    l1_pre_topc(sK2)),
% 1.48/0.59    inference(subsumption_resolution,[],[f98,f45])).
% 1.48/0.59  fof(f45,plain,(
% 1.48/0.59    l1_pre_topc(sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f32,plain,(
% 1.48/0.59    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f31,f30,f29,f28])).
% 1.48/0.59  fof(f28,plain,(
% 1.48/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f29,plain,(
% 1.48/0.59    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f30,plain,(
% 1.48/0.59    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f31,plain,(
% 1.48/0.59    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f16,plain,(
% 1.48/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.48/0.59    inference(flattening,[],[f15])).
% 1.48/0.59  fof(f15,plain,(
% 1.48/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f14])).
% 1.48/0.59  fof(f14,plain,(
% 1.48/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 1.48/0.59    inference(pure_predicate_removal,[],[f12])).
% 1.48/0.59  fof(f12,negated_conjecture,(
% 1.48/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 1.48/0.59    inference(negated_conjecture,[],[f11])).
% 1.48/0.59  fof(f11,conjecture,(
% 1.48/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 1.48/0.59  fof(f98,plain,(
% 1.48/0.59    l1_pre_topc(sK2) | ~l1_pre_topc(sK0)),
% 1.48/0.59    inference(resolution,[],[f55,f47])).
% 1.48/0.59  fof(f47,plain,(
% 1.48/0.59    m1_pre_topc(sK2,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f55,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f19])).
% 1.48/0.59  fof(f19,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f7])).
% 1.48/0.59  fof(f7,axiom,(
% 1.48/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.48/0.59  fof(f1260,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK2) | ~spl6_1),
% 1.48/0.59    inference(subsumption_resolution,[],[f162,f154])).
% 1.48/0.59  fof(f154,plain,(
% 1.48/0.59    l1_struct_0(sK3)),
% 1.48/0.59    inference(resolution,[],[f103,f54])).
% 1.48/0.59  fof(f103,plain,(
% 1.48/0.59    l1_pre_topc(sK3)),
% 1.48/0.59    inference(subsumption_resolution,[],[f99,f45])).
% 1.48/0.59  fof(f99,plain,(
% 1.48/0.59    l1_pre_topc(sK3) | ~l1_pre_topc(sK0)),
% 1.48/0.59    inference(resolution,[],[f55,f48])).
% 1.48/0.59  fof(f48,plain,(
% 1.48/0.59    m1_pre_topc(sK3,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f162,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK2) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | ~spl6_1),
% 1.48/0.59    inference(resolution,[],[f81,f63])).
% 1.48/0.59  fof(f63,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f27])).
% 1.48/0.59  fof(f27,plain,(
% 1.48/0.59    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.48/0.59    inference(flattening,[],[f26])).
% 1.48/0.59  fof(f26,plain,(
% 1.48/0.59    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f9])).
% 1.48/0.59  fof(f9,axiom,(
% 1.48/0.59    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.48/0.59  fof(f81,plain,(
% 1.48/0.59    r1_tsep_1(sK2,sK3) | ~spl6_1),
% 1.48/0.59    inference(avatar_component_clause,[],[f79])).
% 1.48/0.59  fof(f79,plain,(
% 1.48/0.59    spl6_1 <=> r1_tsep_1(sK2,sK3)),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.48/0.59  fof(f84,plain,(
% 1.48/0.59    ~r1_tsep_1(sK3,sK2) | spl6_2),
% 1.48/0.59    inference(avatar_component_clause,[],[f83])).
% 1.48/0.59  fof(f83,plain,(
% 1.48/0.59    spl6_2 <=> r1_tsep_1(sK3,sK2)),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.48/0.59  fof(f1259,plain,(
% 1.48/0.59    ~spl6_2 | spl6_3 | ~spl6_14),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f1258])).
% 1.48/0.59  fof(f1258,plain,(
% 1.48/0.59    $false | (~spl6_2 | spl6_3 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1257,f154])).
% 1.48/0.59  fof(f1257,plain,(
% 1.48/0.59    ~l1_struct_0(sK3) | (~spl6_2 | spl6_3 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1256,f109])).
% 1.48/0.59  fof(f109,plain,(
% 1.48/0.59    l1_struct_0(sK1)),
% 1.48/0.59    inference(resolution,[],[f101,f54])).
% 1.48/0.59  fof(f101,plain,(
% 1.48/0.59    l1_pre_topc(sK1)),
% 1.48/0.59    inference(subsumption_resolution,[],[f97,f45])).
% 1.48/0.59  fof(f97,plain,(
% 1.48/0.59    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 1.48/0.59    inference(resolution,[],[f55,f46])).
% 1.48/0.59  fof(f46,plain,(
% 1.48/0.59    m1_pre_topc(sK1,sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f1256,plain,(
% 1.48/0.59    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | (~spl6_2 | spl6_3 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1255,f90])).
% 1.48/0.59  fof(f90,plain,(
% 1.48/0.59    ~r1_tsep_1(sK1,sK3) | spl6_3),
% 1.48/0.59    inference(avatar_component_clause,[],[f88])).
% 1.48/0.59  fof(f88,plain,(
% 1.48/0.59    spl6_3 <=> r1_tsep_1(sK1,sK3)),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.48/0.59  fof(f1255,plain,(
% 1.48/0.59    r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | (~spl6_2 | ~spl6_14)),
% 1.48/0.59    inference(resolution,[],[f1120,f63])).
% 1.48/0.59  fof(f1120,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK1) | (~spl6_2 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1119,f154])).
% 1.48/0.59  fof(f1119,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK3) | (~spl6_2 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1113,f109])).
% 1.48/0.59  fof(f1113,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK1) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | (~spl6_2 | ~spl6_14)),
% 1.48/0.59    inference(resolution,[],[f1040,f53])).
% 1.48/0.59  fof(f53,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f33])).
% 1.48/0.59  fof(f33,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.48/0.59    inference(nnf_transformation,[],[f17])).
% 1.48/0.59  fof(f17,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.48/0.59    inference(ennf_transformation,[],[f8])).
% 1.48/0.59  fof(f8,axiom,(
% 1.48/0.59    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.48/0.59  fof(f1040,plain,(
% 1.48/0.59    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | (~spl6_2 | ~spl6_14)),
% 1.48/0.59    inference(superposition,[],[f888,f228])).
% 1.48/0.59  fof(f228,plain,(
% 1.48/0.59    u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_14),
% 1.48/0.59    inference(resolution,[],[f199,f62])).
% 1.48/0.59  fof(f62,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.48/0.59    inference(cnf_transformation,[],[f25])).
% 1.48/0.59  fof(f25,plain,(
% 1.48/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.48/0.59    inference(ennf_transformation,[],[f4])).
% 1.48/0.59  fof(f4,axiom,(
% 1.48/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.48/0.59  fof(f199,plain,(
% 1.48/0.59    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl6_14),
% 1.48/0.59    inference(avatar_component_clause,[],[f197])).
% 1.48/0.59  fof(f197,plain,(
% 1.48/0.59    spl6_14 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.48/0.59  fof(f888,plain,(
% 1.48/0.59    ( ! [X0] : (r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2)))) ) | ~spl6_2),
% 1.48/0.59    inference(duplicate_literal_removal,[],[f885])).
% 1.48/0.59  fof(f885,plain,(
% 1.48/0.59    ( ! [X0] : (r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2))) | r1_xboole_0(u1_struct_0(sK3),k3_xboole_0(X0,u1_struct_0(sK2)))) ) | ~spl6_2),
% 1.48/0.59    inference(resolution,[],[f622,f106])).
% 1.48/0.59  fof(f106,plain,(
% 1.48/0.59    ( ! [X4,X5,X3] : (r2_hidden(sK4(X3,k3_xboole_0(X4,X5)),X5) | r1_xboole_0(X3,k3_xboole_0(X4,X5))) )),
% 1.48/0.59    inference(resolution,[],[f76,f60])).
% 1.48/0.59  fof(f60,plain,(
% 1.48/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f36])).
% 1.48/0.59  fof(f36,plain,(
% 1.48/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f35])).
% 1.48/0.59  fof(f35,plain,(
% 1.48/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f24,plain,(
% 1.48/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.48/0.59    inference(ennf_transformation,[],[f13])).
% 1.48/0.59  fof(f13,plain,(
% 1.48/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.59    inference(rectify,[],[f2])).
% 1.48/0.59  fof(f2,axiom,(
% 1.48/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.48/0.59  fof(f76,plain,(
% 1.48/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.48/0.59    inference(equality_resolution,[],[f68])).
% 1.48/0.59  fof(f68,plain,(
% 1.48/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.48/0.59    inference(cnf_transformation,[],[f43])).
% 1.48/0.59  fof(f43,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.48/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.48/0.59  fof(f42,plain,(
% 1.48/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.48/0.59    introduced(choice_axiom,[])).
% 1.48/0.59  fof(f41,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.48/0.59    inference(rectify,[],[f40])).
% 1.48/0.59  fof(f40,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.48/0.59    inference(flattening,[],[f39])).
% 1.48/0.59  fof(f39,plain,(
% 1.48/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.48/0.59    inference(nnf_transformation,[],[f1])).
% 1.48/0.59  fof(f1,axiom,(
% 1.48/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.48/0.59  fof(f622,plain,(
% 1.48/0.59    ( ! [X0] : (~r2_hidden(sK4(u1_struct_0(sK3),X0),u1_struct_0(sK2)) | r1_xboole_0(u1_struct_0(sK3),X0)) ) | ~spl6_2),
% 1.48/0.59    inference(resolution,[],[f210,f59])).
% 1.48/0.59  fof(f59,plain,(
% 1.48/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f36])).
% 1.48/0.59  fof(f210,plain,(
% 1.48/0.59    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | ~spl6_2),
% 1.48/0.59    inference(resolution,[],[f160,f61])).
% 1.48/0.59  fof(f61,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f36])).
% 1.48/0.59  fof(f160,plain,(
% 1.48/0.59    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~spl6_2),
% 1.48/0.59    inference(subsumption_resolution,[],[f159,f154])).
% 1.48/0.59  fof(f159,plain,(
% 1.48/0.59    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK3) | ~spl6_2),
% 1.48/0.59    inference(subsumption_resolution,[],[f137,f134])).
% 1.48/0.59  fof(f137,plain,(
% 1.48/0.59    r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) | ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | ~spl6_2),
% 1.48/0.59    inference(resolution,[],[f52,f85])).
% 1.48/0.59  fof(f85,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK2) | ~spl6_2),
% 1.48/0.59    inference(avatar_component_clause,[],[f83])).
% 1.48/0.59  fof(f52,plain,(
% 1.48/0.59    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f33])).
% 1.48/0.59  fof(f1118,plain,(
% 1.48/0.59    ~spl6_2 | spl6_4 | ~spl6_14),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f1117])).
% 1.48/0.59  fof(f1117,plain,(
% 1.48/0.59    $false | (~spl6_2 | spl6_4 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1116,f154])).
% 1.48/0.59  fof(f1116,plain,(
% 1.48/0.59    ~l1_struct_0(sK3) | (~spl6_2 | spl6_4 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1115,f109])).
% 1.48/0.59  fof(f1115,plain,(
% 1.48/0.59    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | (~spl6_2 | spl6_4 | ~spl6_14)),
% 1.48/0.59    inference(subsumption_resolution,[],[f1113,f94])).
% 1.48/0.59  fof(f94,plain,(
% 1.48/0.59    ~r1_tsep_1(sK3,sK1) | spl6_4),
% 1.48/0.59    inference(avatar_component_clause,[],[f92])).
% 1.48/0.59  fof(f92,plain,(
% 1.48/0.59    spl6_4 <=> r1_tsep_1(sK3,sK1)),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.48/0.59  fof(f225,plain,(
% 1.48/0.59    ~spl6_13),
% 1.48/0.59    inference(avatar_contradiction_clause,[],[f224])).
% 1.48/0.59  fof(f224,plain,(
% 1.48/0.59    $false | ~spl6_13),
% 1.48/0.59    inference(subsumption_resolution,[],[f223,f46])).
% 1.48/0.59  fof(f223,plain,(
% 1.48/0.59    ~m1_pre_topc(sK1,sK0) | ~spl6_13),
% 1.48/0.59    inference(subsumption_resolution,[],[f222,f45])).
% 1.48/0.59  fof(f222,plain,(
% 1.48/0.59    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl6_13),
% 1.48/0.59    inference(subsumption_resolution,[],[f221,f44])).
% 1.48/0.59  fof(f44,plain,(
% 1.48/0.59    v2_pre_topc(sK0)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f221,plain,(
% 1.48/0.59    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl6_13),
% 1.48/0.59    inference(resolution,[],[f195,f47])).
% 1.48/0.59  fof(f195,plain,(
% 1.48/0.59    ( ! [X3] : (~m1_pre_topc(sK2,X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK1,X3)) ) | ~spl6_13),
% 1.48/0.59    inference(avatar_component_clause,[],[f194])).
% 1.48/0.59  fof(f194,plain,(
% 1.48/0.59    spl6_13 <=> ! [X3] : (~m1_pre_topc(sK2,X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(sK1,X3))),
% 1.48/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.48/0.59  fof(f200,plain,(
% 1.48/0.59    spl6_13 | spl6_14),
% 1.48/0.59    inference(avatar_split_clause,[],[f168,f197,f194])).
% 1.48/0.59  fof(f168,plain,(
% 1.48/0.59    ( ! [X3] : (r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,X3) | ~m1_pre_topc(sK1,X3) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) )),
% 1.48/0.59    inference(resolution,[],[f58,f49])).
% 1.48/0.59  fof(f49,plain,(
% 1.48/0.59    m1_pre_topc(sK1,sK2)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f58,plain,(
% 1.48/0.59    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.48/0.59    inference(cnf_transformation,[],[f34])).
% 1.48/0.59  fof(f34,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.59    inference(nnf_transformation,[],[f23])).
% 1.48/0.59  fof(f23,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.48/0.59    inference(flattening,[],[f22])).
% 1.48/0.59  fof(f22,plain,(
% 1.48/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.48/0.59    inference(ennf_transformation,[],[f10])).
% 1.48/0.59  fof(f10,axiom,(
% 1.48/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.48/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.48/0.59  fof(f95,plain,(
% 1.48/0.59    ~spl6_3 | ~spl6_4),
% 1.48/0.59    inference(avatar_split_clause,[],[f50,f92,f88])).
% 1.48/0.59  fof(f50,plain,(
% 1.48/0.59    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  fof(f86,plain,(
% 1.48/0.59    spl6_1 | spl6_2),
% 1.48/0.59    inference(avatar_split_clause,[],[f51,f83,f79])).
% 1.48/0.59  fof(f51,plain,(
% 1.48/0.59    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 1.48/0.59    inference(cnf_transformation,[],[f32])).
% 1.48/0.59  % SZS output end Proof for theBenchmark
% 1.48/0.59  % (19801)------------------------------
% 1.48/0.59  % (19801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.59  % (19801)Termination reason: Refutation
% 1.48/0.59  
% 1.48/0.59  % (19801)Memory used [KB]: 11385
% 1.48/0.59  % (19801)Time elapsed: 0.150 s
% 1.48/0.59  % (19801)------------------------------
% 1.48/0.59  % (19801)------------------------------
% 1.48/0.59  % (19790)Success in time 0.215 s
%------------------------------------------------------------------------------
