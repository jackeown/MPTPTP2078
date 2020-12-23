%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 532 expanded)
%              Number of leaves         :   21 ( 144 expanded)
%              Depth                    :   18
%              Number of atoms          :  510 (2682 expanded)
%              Number of equality atoms :   55 ( 409 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f245,f256,f337,f381])).

fof(f381,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f379,f374])).

fof(f374,plain,(
    ~ r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f291,f214])).

fof(f214,plain,(
    ! [X37] :
      ( ~ r2_orders_2(sK0,X37,X37)
      | ~ m1_subset_1(X37,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f170,f55])).

fof(f55,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f170,plain,(
    ! [X37] :
      ( ~ m1_subset_1(X37,k2_struct_0(sK0))
      | ~ r2_orders_2(sK0,X37,X37)
      | ~ l1_orders_2(sK0) ) ),
    inference(superposition,[],[f86,f95])).

fof(f95,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f55,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f291,plain,(
    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f98,f94,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,(
    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ( ( r2_hidden(X4,X1)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_mcart_1)).

fof(f56,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    m1_subset_1(k1_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f92,f95])).

fof(f92,plain,(
    m1_subset_1(k1_orders_2(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f91,plain,(
    m1_subset_1(k1_orders_2(sK0,k2_subset_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f52,f53,f54,f60,f55,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f379,plain,
    ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f375,f339])).

fof(f339,plain,
    ( sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f94,f244])).

fof(f244,plain,
    ( ! [X1] :
        ( sK4(X1,sK0,k2_struct_0(sK0)) = X1
        | ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl5_3
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
        | sK4(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f375,plain,
    ( r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f94,f302,f255])).

fof(f255,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k2_struct_0(sK0))
        | ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
        | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl5_4
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
        | ~ r2_hidden(X3,k2_struct_0(sK0))
        | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f302,plain,(
    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f94,f150,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f150,plain,(
    r1_tarski(k1_orders_2(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f98,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f337,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f334,f335])).

fof(f335,plain,
    ( ~ r2_hidden(sK2(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f296,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f296,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f234,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f234,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl5_2
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f334,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f296,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f256,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f252,f232,f254])).

fof(f252,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f251,f95])).

fof(f251,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f250,f81])).

fof(f250,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f249,f51])).

fof(f249,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f248,f52])).

fof(f248,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f247,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f246,f54])).

fof(f246,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f217,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0)))
      | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))
      | ~ r2_hidden(X3,k2_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f96])).

fof(f96,plain,(
    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f93,f95])).

fof(f93,plain,(
    k1_orders_2(sK0,u1_struct_0(sK0)) = a_2_0_orders_2(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f89,f58])).

fof(f89,plain,(
    k1_orders_2(sK0,k2_subset_1(u1_struct_0(sK0))) = a_2_0_orders_2(sK0,k2_subset_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f52,f53,f54,f60,f55,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f77,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f245,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f241,f232,f243])).

fof(f241,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1 ) ),
    inference(forward_demodulation,[],[f240,f95])).

fof(f240,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f239,f51])).

fof(f239,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f52])).

fof(f238,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f53])).

fof(f237,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f54])).

fof(f236,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f216,f55])).

fof(f216,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))
      | sK4(X1,sK0,k2_struct_0(sK0)) = X1
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f76,f96])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sK4(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:35:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (333)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (342)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (323)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (332)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (344)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (336)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (331)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (344)Refutation not found, incomplete strategy% (344)------------------------------
% 0.21/0.52  % (344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (344)Memory used [KB]: 10746
% 0.21/0.52  % (344)Time elapsed: 0.066 s
% 0.21/0.52  % (344)------------------------------
% 0.21/0.52  % (344)------------------------------
% 0.21/0.52  % (326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (350)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (334)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (330)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (324)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (322)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (351)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (327)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (325)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (346)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (340)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (337)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (328)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (343)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (345)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (341)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (335)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (339)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (329)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (349)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (347)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (348)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (338)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (348)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f382,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f245,f256,f337,f381])).
% 0.21/0.59  fof(f381,plain,(
% 0.21/0.59    ~spl5_3 | ~spl5_4),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.59  fof(f380,plain,(
% 0.21/0.59    $false | (~spl5_3 | ~spl5_4)),
% 0.21/0.59    inference(subsumption_resolution,[],[f379,f374])).
% 0.21/0.59  fof(f374,plain,(
% 0.21/0.59    ~r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0))))),
% 0.21/0.59    inference(unit_resulting_resolution,[],[f291,f214])).
% 0.21/0.59  fof(f214,plain,(
% 0.21/0.59    ( ! [X37] : (~r2_orders_2(sK0,X37,X37) | ~m1_subset_1(X37,k2_struct_0(sK0))) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f170,f55])).
% 0.21/0.59  fof(f55,plain,(
% 0.21/0.59    l1_orders_2(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f36,plain,(
% 1.69/0.59    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).
% 1.69/0.59  fof(f35,plain,(
% 1.69/0.59    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f20,plain,(
% 1.69/0.59    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.69/0.59    inference(flattening,[],[f19])).
% 1.69/0.59  fof(f19,plain,(
% 1.69/0.59    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f17])).
% 1.69/0.59  fof(f17,negated_conjecture,(
% 1.69/0.59    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.69/0.59    inference(negated_conjecture,[],[f16])).
% 1.69/0.59  fof(f16,conjecture,(
% 1.69/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 1.69/0.59  fof(f170,plain,(
% 1.69/0.59    ( ! [X37] : (~m1_subset_1(X37,k2_struct_0(sK0)) | ~r2_orders_2(sK0,X37,X37) | ~l1_orders_2(sK0)) )),
% 1.69/0.59    inference(superposition,[],[f86,f95])).
% 1.69/0.59  fof(f95,plain,(
% 1.69/0.59    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f87,f61])).
% 1.69/0.59  fof(f61,plain,(
% 1.69/0.59    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f21])).
% 1.69/0.59  fof(f21,plain,(
% 1.69/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f10])).
% 1.69/0.59  fof(f10,axiom,(
% 1.69/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.69/0.59  fof(f87,plain,(
% 1.69/0.59    l1_struct_0(sK0)),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f55,f62])).
% 1.69/0.59  fof(f62,plain,(
% 1.69/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f22,plain,(
% 1.69/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f14])).
% 1.69/0.59  fof(f14,axiom,(
% 1.69/0.59    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.69/0.59  fof(f86,plain,(
% 1.69/0.59    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.69/0.59    inference(duplicate_literal_removal,[],[f82])).
% 1.69/0.59  fof(f82,plain,(
% 1.69/0.59    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.69/0.59    inference(equality_resolution,[],[f64])).
% 1.69/0.59  fof(f64,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f38])).
% 1.69/0.59  fof(f38,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.69/0.59    inference(flattening,[],[f37])).
% 1.69/0.59  fof(f37,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.69/0.59    inference(nnf_transformation,[],[f23])).
% 1.69/0.59  fof(f23,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.69/0.59    inference(ennf_transformation,[],[f11])).
% 1.69/0.59  fof(f11,axiom,(
% 1.69/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 1.69/0.59  fof(f291,plain,(
% 1.69/0.59    m1_subset_1(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f98,f94,f81])).
% 1.69/0.59  fof(f81,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f34])).
% 1.69/0.59  fof(f34,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.69/0.59    inference(flattening,[],[f33])).
% 1.69/0.59  fof(f33,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f7])).
% 1.69/0.59  fof(f7,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.69/0.59  fof(f94,plain,(
% 1.69/0.59    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k1_orders_2(sK0,k2_struct_0(sK0)))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f56,f67])).
% 1.69/0.59  fof(f67,plain,(
% 1.69/0.59    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f40])).
% 1.69/0.59  fof(f40,plain,(
% 1.69/0.59    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f39])).
% 1.69/0.59  fof(f39,plain,(
% 1.69/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.69/0.59    inference(ennf_transformation,[],[f18])).
% 1.69/0.59  fof(f18,plain,(
% 1.69/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.69/0.59    inference(pure_predicate_removal,[],[f9])).
% 1.69/0.59  fof(f9,axiom,(
% 1.69/0.59    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ((r2_hidden(X4,X1) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_mcart_1)).
% 1.69/0.59  fof(f56,plain,(
% 1.69/0.59    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))),
% 1.69/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f98,plain,(
% 1.69/0.59    m1_subset_1(k1_orders_2(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.69/0.59    inference(backward_demodulation,[],[f92,f95])).
% 1.69/0.59  fof(f92,plain,(
% 1.69/0.59    m1_subset_1(k1_orders_2(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.69/0.59    inference(forward_demodulation,[],[f91,f58])).
% 1.69/0.59  fof(f58,plain,(
% 1.69/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f3])).
% 1.69/0.59  fof(f3,axiom,(
% 1.69/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.69/0.59  fof(f91,plain,(
% 1.69/0.59    m1_subset_1(k1_orders_2(sK0,k2_subset_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f51,f52,f53,f54,f60,f55,f68])).
% 1.69/0.59  fof(f68,plain,(
% 1.69/0.59    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f28])).
% 1.69/0.59  fof(f28,plain,(
% 1.69/0.59    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.69/0.59    inference(flattening,[],[f27])).
% 1.69/0.59  fof(f27,plain,(
% 1.69/0.59    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f13])).
% 1.69/0.59  fof(f13,axiom,(
% 1.69/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 1.69/0.59  fof(f60,plain,(
% 1.69/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f4])).
% 1.69/0.59  fof(f4,axiom,(
% 1.69/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.69/0.59  fof(f54,plain,(
% 1.69/0.59    v5_orders_2(sK0)),
% 1.69/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f53,plain,(
% 1.69/0.59    v4_orders_2(sK0)),
% 1.69/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    v3_orders_2(sK0)),
% 1.69/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f51,plain,(
% 1.69/0.59    ~v2_struct_0(sK0)),
% 1.69/0.59    inference(cnf_transformation,[],[f36])).
% 1.69/0.59  fof(f379,plain,(
% 1.69/0.59    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK1(k1_orders_2(sK0,k2_struct_0(sK0)))) | (~spl5_3 | ~spl5_4)),
% 1.69/0.59    inference(forward_demodulation,[],[f375,f339])).
% 1.69/0.59  fof(f339,plain,(
% 1.69/0.59    sK1(k1_orders_2(sK0,k2_struct_0(sK0))) = sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0)) | ~spl5_3),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f94,f244])).
% 1.69/0.59  fof(f244,plain,(
% 1.69/0.59    ( ! [X1] : (sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0)))) ) | ~spl5_3),
% 1.69/0.59    inference(avatar_component_clause,[],[f243])).
% 1.69/0.59  fof(f243,plain,(
% 1.69/0.59    spl5_3 <=> ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.69/0.59  fof(f375,plain,(
% 1.69/0.59    r2_orders_2(sK0,sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK4(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),sK0,k2_struct_0(sK0))) | ~spl5_4),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f94,f302,f255])).
% 1.69/0.59  fof(f255,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k2_struct_0(sK0)) | ~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0)))) ) | ~spl5_4),
% 1.69/0.59    inference(avatar_component_clause,[],[f254])).
% 1.69/0.59  fof(f254,plain,(
% 1.69/0.59    spl5_4 <=> ! [X3,X2] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.69/0.59  fof(f302,plain,(
% 1.69/0.59    r2_hidden(sK1(k1_orders_2(sK0,k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f94,f150,f69])).
% 1.69/0.59  fof(f69,plain,(
% 1.69/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f44])).
% 1.69/0.59  fof(f44,plain,(
% 1.69/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 1.69/0.59  fof(f43,plain,(
% 1.69/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f42,plain,(
% 1.69/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.59    inference(rectify,[],[f41])).
% 1.69/0.59  fof(f41,plain,(
% 1.69/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.69/0.59    inference(nnf_transformation,[],[f29])).
% 1.69/0.59  fof(f29,plain,(
% 1.69/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f1])).
% 1.69/0.59  fof(f1,axiom,(
% 1.69/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.69/0.59  fof(f150,plain,(
% 1.69/0.59    r1_tarski(k1_orders_2(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f98,f72])).
% 1.69/0.59  fof(f72,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f45])).
% 1.69/0.59  fof(f45,plain,(
% 1.69/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.69/0.59    inference(nnf_transformation,[],[f6])).
% 1.69/0.59  fof(f6,axiom,(
% 1.69/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.69/0.59  fof(f337,plain,(
% 1.69/0.59    spl5_2),
% 1.69/0.59    inference(avatar_contradiction_clause,[],[f336])).
% 1.69/0.59  fof(f336,plain,(
% 1.69/0.59    $false | spl5_2),
% 1.69/0.59    inference(subsumption_resolution,[],[f334,f335])).
% 1.69/0.59  fof(f335,plain,(
% 1.69/0.59    ~r2_hidden(sK2(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) | spl5_2),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f296,f71])).
% 1.69/0.59  fof(f71,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f44])).
% 1.69/0.59  fof(f296,plain,(
% 1.69/0.59    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | spl5_2),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f234,f73])).
% 1.69/0.59  fof(f73,plain,(
% 1.69/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f45])).
% 1.69/0.59  fof(f234,plain,(
% 1.69/0.59    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | spl5_2),
% 1.69/0.59    inference(avatar_component_clause,[],[f232])).
% 1.69/0.59  fof(f232,plain,(
% 1.69/0.59    spl5_2 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.69/0.59  fof(f334,plain,(
% 1.69/0.59    r2_hidden(sK2(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) | spl5_2),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f296,f70])).
% 1.69/0.59  fof(f70,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f44])).
% 1.69/0.59  fof(f256,plain,(
% 1.69/0.59    spl5_4 | ~spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f252,f232,f254])).
% 1.69/0.59  fof(f252,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f251,f95])).
% 1.69/0.59  fof(f251,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f250,f81])).
% 1.69/0.59  fof(f250,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f249,f51])).
% 1.69/0.59  fof(f249,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f248,f52])).
% 1.69/0.59  fof(f248,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f247,f53])).
% 1.69/0.59  fof(f247,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f246,f54])).
% 1.69/0.59  fof(f246,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f217,f55])).
% 1.69/0.59  fof(f217,plain,(
% 1.69/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_orders_2(sK0,k2_struct_0(sK0))) | r2_orders_2(sK0,X3,sK4(X2,sK0,k2_struct_0(sK0))) | ~r2_hidden(X3,k2_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(superposition,[],[f77,f96])).
% 1.69/0.59  fof(f96,plain,(
% 1.69/0.59    k1_orders_2(sK0,k2_struct_0(sK0)) = a_2_0_orders_2(sK0,k2_struct_0(sK0))),
% 1.69/0.59    inference(backward_demodulation,[],[f93,f95])).
% 1.69/0.59  fof(f93,plain,(
% 1.69/0.59    k1_orders_2(sK0,u1_struct_0(sK0)) = a_2_0_orders_2(sK0,u1_struct_0(sK0))),
% 1.69/0.59    inference(forward_demodulation,[],[f89,f58])).
% 1.69/0.59  fof(f89,plain,(
% 1.69/0.59    k1_orders_2(sK0,k2_subset_1(u1_struct_0(sK0))) = a_2_0_orders_2(sK0,k2_subset_1(u1_struct_0(sK0)))),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f51,f52,f53,f54,f60,f55,f66])).
% 1.69/0.59  fof(f66,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.69/0.59    inference(flattening,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f12])).
% 1.69/0.59  fof(f12,axiom,(
% 1.69/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 1.69/0.59  fof(f77,plain,(
% 1.69/0.59    ( ! [X6,X2,X0,X1] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f50])).
% 1.69/0.59  fof(f50,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).
% 1.69/0.59  fof(f48,plain,(
% 1.69/0.59    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f49,plain,(
% 1.69/0.59    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f47,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.69/0.59    inference(rectify,[],[f46])).
% 1.69/0.59  fof(f46,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.69/0.59    inference(nnf_transformation,[],[f32])).
% 1.69/0.59  fof(f32,plain,(
% 1.69/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.69/0.59    inference(flattening,[],[f31])).
% 1.69/0.59  fof(f31,plain,(
% 1.69/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f15])).
% 1.69/0.59  fof(f15,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.69/0.59  fof(f245,plain,(
% 1.69/0.59    spl5_3 | ~spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f241,f232,f243])).
% 1.69/0.59  fof(f241,plain,(
% 1.69/0.59    ( ! [X1] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1) )),
% 1.69/0.59    inference(forward_demodulation,[],[f240,f95])).
% 1.69/0.59  fof(f240,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f239,f51])).
% 1.69/0.59  fof(f239,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f238,f52])).
% 1.69/0.59  fof(f238,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f237,f53])).
% 1.69/0.59  fof(f237,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f236,f54])).
% 1.69/0.59  fof(f236,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(subsumption_resolution,[],[f216,f55])).
% 1.69/0.59  fof(f216,plain,(
% 1.69/0.59    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK0,k2_struct_0(sK0))) | sK4(X1,sK0,k2_struct_0(sK0)) = X1 | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.69/0.59    inference(superposition,[],[f76,f96])).
% 1.69/0.59  fof(f76,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (sK4(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f50])).
% 1.69/0.59  % SZS output end Proof for theBenchmark
% 1.69/0.59  % (348)------------------------------
% 1.69/0.59  % (348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (348)Termination reason: Refutation
% 1.69/0.59  
% 1.69/0.59  % (348)Memory used [KB]: 10874
% 1.69/0.59  % (348)Time elapsed: 0.168 s
% 1.69/0.59  % (348)------------------------------
% 1.69/0.59  % (348)------------------------------
% 1.69/0.60  % (321)Success in time 0.234 s
%------------------------------------------------------------------------------
