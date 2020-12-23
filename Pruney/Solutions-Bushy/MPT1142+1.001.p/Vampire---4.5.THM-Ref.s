%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1142+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 546 expanded)
%              Number of leaves         :   16 ( 230 expanded)
%              Depth                    :   14
%              Number of atoms          :  498 (5163 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f57,f148,f183,f187,f277,f291,f306,f324,f413,f421,f430])).

fof(f430,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f240,f418])).

fof(f418,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f45,f147])).

fof(f147,plain,
    ( sK1 = sK3
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl4_6
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f45,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f240,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f239,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & ( ( r2_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( r1_orders_2(sK0,sK2,sK3)
        & r2_orders_2(sK0,sK1,sK2) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & ( ( r2_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( r1_orders_2(sK0,X2,X3)
                      & r2_orders_2(sK0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(sK0,X1,X3)
                & ( ( r2_orders_2(sK0,X2,X3)
                    & r1_orders_2(sK0,X1,X2) )
                  | ( r1_orders_2(sK0,X2,X3)
                    & r2_orders_2(sK0,X1,X2) ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(sK0,sK1,X3)
              & ( ( r2_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,sK1,X2) )
                | ( r1_orders_2(sK0,X2,X3)
                  & r2_orders_2(sK0,sK1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_orders_2(sK0,sK1,X3)
            & ( ( r2_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,sK1,X2) )
              | ( r1_orders_2(sK0,X2,X3)
                & r2_orders_2(sK0,sK1,X2) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_orders_2(sK0,sK1,X3)
          & ( ( r2_orders_2(sK0,sK2,X3)
              & r1_orders_2(sK0,sK1,sK2) )
            | ( r1_orders_2(sK0,sK2,X3)
              & r2_orders_2(sK0,sK1,sK2) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        & ( ( r2_orders_2(sK0,sK2,X3)
            & r1_orders_2(sK0,sK1,sK2) )
          | ( r1_orders_2(sK0,sK2,X3)
            & r2_orders_2(sK0,sK1,sK2) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_orders_2(sK0,sK1,sK3)
      & ( ( r2_orders_2(sK0,sK2,sK3)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( r1_orders_2(sK0,sK2,sK3)
          & r2_orders_2(sK0,sK1,sK2) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(f239,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f238,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f238,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f233,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f233,plain,
    ( ~ r2_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl4_7 ),
    inference(resolution,[],[f173,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

% (29392)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f173,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_7
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f421,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f419,f89])).

fof(f89,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f76,f22])).

fof(f76,plain,
    ( ~ r2_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f419,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f418,f177])).

fof(f177,plain,
    ( sK1 = sK2
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_8
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f413,plain,
    ( ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f411,f89])).

fof(f411,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f50,f177])).

fof(f50,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_3
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f324,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f309,f173])).

fof(f309,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f41,f147])).

fof(f41,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f306,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f54,f304])).

fof(f304,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f262,f23])).

fof(f262,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f101,f50])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r2_orders_2(sK0,X1,sK2)
      | r1_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f22])).

fof(f91,plain,(
    ! [X1] :
      ( r1_orders_2(sK0,X1,sK2)
      | ~ r2_orders_2(sK0,X1,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f24,f31])).

fof(f54,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_4
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f291,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f289,f25])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f289,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f283,f143])).

fof(f143,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_5
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f283,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f41,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f160,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f160,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f159,f22])).

fof(f159,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f158,f23])).

fof(f158,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f153,f24])).

fof(f153,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f55,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f277,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f275,f25])).

fof(f275,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f270,f143])).

fof(f270,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f161,f152])).

fof(f152,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f151,f22])).

fof(f151,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f150,f24])).

fof(f150,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f149,f25])).

fof(f149,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f45,f31])).

fof(f187,plain,
    ( spl4_8
    | spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f186,f53,f48,f175])).

fof(f186,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f185,f22])).

fof(f185,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2
    | ~ l1_orders_2(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f184,f23])).

fof(f184,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f157,f24])).

fof(f157,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK2
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f183,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f182,f53,f175,f171])).

fof(f182,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f181,f21])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f181,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f180,f22])).

fof(f180,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f179,f24])).

fof(f179,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f156,f23])).

fof(f156,plain,
    ( sK1 = sK2
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f148,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f139,f145,f141])).

fof(f139,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f138,f22])).

fof(f138,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f137,f23])).

fof(f137,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f136,f25])).

fof(f136,plain,
    ( sK1 = sK3
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f30,f33])).

fof(f30,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f26,f53,f48])).

fof(f26,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f28,f43,f48])).

fof(f28,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f29,f43,f39])).

fof(f29,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
