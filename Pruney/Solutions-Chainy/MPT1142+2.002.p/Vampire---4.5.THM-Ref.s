%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 421 expanded)
%              Number of leaves         :   13 ( 191 expanded)
%              Depth                    :   15
%              Number of atoms          :  330 (4164 expanded)
%              Number of equality atoms :    9 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f69,f166,f185,f214])).

fof(f214,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f208,f66])).

fof(f66,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_4
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f208,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f62,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

% (6913)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f62,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_3
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f23,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f185,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f175,f62])).

fof(f175,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f46,f46,f30,f169,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_orders_2(X0,X2,X4)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X4,X5)
      | ~ sQ4_eqProxy(X0,X1)
      | r2_orders_2(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f169,plain,
    ( sQ4_eqProxy(sK2,sK3)
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f22,f24,f25,f53,f56,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | sQ4_eqProxy(X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(equality_proxy_replacement,[],[f33,f37])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_2
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f53,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_1
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f25,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f166,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f139,f25])).

fof(f139,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f20,f22,f114,f103,f23,f67,f24,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f67,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f103,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f22,f24,f57,f25,f31])).

fof(f57,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f114,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f22,f30,f23,f25,f112,f38])).

fof(f112,plain,
    ( ~ sQ4_eqProxy(sK1,sK3)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f67,f46,f46,f108,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X4)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X4,X5)
      | ~ sQ4_eqProxy(X0,X1)
      | r1_orders_2(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f108,plain,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f22,f88,f106,f25,f24,f38])).

fof(f106,plain,
    ( ~ r2_orders_2(sK0,sK3,sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f21,f22,f24,f57,f25,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,
    ( ~ sQ4_eqProxy(sK3,sK2)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f77,f46,f46,f57,f42])).

fof(f77,plain,(
    ~ r2_orders_2(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f22,f24,f49])).

fof(f49,plain,(
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

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f26,f65,f60])).

fof(f26,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f28,f55,f60])).

fof(f28,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f55,f51])).

fof(f29,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (6916)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (6908)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (6905)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (6904)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (6916)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f58,f63,f69,f166,f185,f214])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ~spl5_3 | spl5_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    $false | (~spl5_3 | spl5_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f208,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ~r1_orders_2(sK0,sK1,sK2) | spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl5_4 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    r1_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f23,f24,f62,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.20/0.48  % (6913)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK1,sK2) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl5_3 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    (((~r2_orders_2(sK0,sK1,sK3) & ((r2_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,sK3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(sK0,X1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,X1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(sK0,X1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,X1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,sK1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X2] : (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2)) | (r1_orders_2(sK0,X2,X3) & r2_orders_2(sK0,sK1,X2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,X3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X3] : (~r2_orders_2(sK0,sK1,X3) & ((r2_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,X3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r2_orders_2(sK0,sK1,sK3) & ((r2_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2)) | (r1_orders_2(sK0,sK2,sK3) & r2_orders_2(sK0,sK1,sK2))) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_orders_2(X0,X1,X3) & ((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2)))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    l1_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ~spl5_1 | spl5_2 | ~spl5_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f184])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    $false | (~spl5_1 | spl5_2 | ~spl5_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f175,f62])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ~r2_orders_2(sK0,sK1,sK2) | (~spl5_1 | spl5_2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f46,f46,f30,f169,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_orders_2(X0,X2,X4) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X4,X5) | ~sQ4_eqProxy(X0,X1) | r2_orders_2(X1,X3,X5)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    sQ4_eqProxy(sK2,sK3) | (~spl5_1 | spl5_2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f24,f25,f53,f56,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | sQ4_eqProxy(X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(X0,X1,X2)) )),
% 0.20/0.48    inference(equality_proxy_replacement,[],[f33,f37])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~r2_orders_2(sK0,sK2,sK3) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl5_2 <=> r2_orders_2(sK0,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    r1_orders_2(sK0,sK2,sK3) | ~spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl5_1 <=> r1_orders_2(sK0,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~r2_orders_2(sK0,sK1,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f37])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ~spl5_2 | ~spl5_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f165])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    $false | (~spl5_2 | ~spl5_4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f139,f25])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl5_2 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f20,f22,f114,f103,f23,f67,f24,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    r1_orders_2(sK0,sK1,sK2) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    r1_orders_2(sK0,sK2,sK3) | ~spl5_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f24,f57,f25,f31])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK2,sK3) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ~r1_orders_2(sK0,sK1,sK3) | (~spl5_2 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f30,f23,f25,f112,f38])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~sQ4_eqProxy(sK1,sK3) | (~spl5_2 | ~spl5_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f67,f46,f46,f108,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_orders_2(X0,X2,X4) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X4,X5) | ~sQ4_eqProxy(X0,X1) | r1_orders_2(X1,X3,X5)) )),
% 0.20/0.48    inference(equality_proxy_axiom,[],[f37])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~r1_orders_2(sK0,sK3,sK2) | ~spl5_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f88,f106,f25,f24,f38])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ~r2_orders_2(sK0,sK3,sK2) | ~spl5_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f21,f22,f24,f57,f25,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_orders_2(X0,X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v5_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~sQ4_eqProxy(sK3,sK2) | ~spl5_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f77,f46,f46,f57,f42])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~r2_orders_2(sK0,sK2,sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f24,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    v4_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl5_3 | spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f65,f60])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    r1_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_3 | spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f55,f60])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_1 | spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f55,f51])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r2_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (6916)------------------------------
% 0.20/0.48  % (6916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6916)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (6916)Memory used [KB]: 10618
% 0.20/0.48  % (6916)Time elapsed: 0.067 s
% 0.20/0.48  % (6916)------------------------------
% 0.20/0.48  % (6916)------------------------------
% 0.20/0.48  % (6901)Success in time 0.127 s
%------------------------------------------------------------------------------
