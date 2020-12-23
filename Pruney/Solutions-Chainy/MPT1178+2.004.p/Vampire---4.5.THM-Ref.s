%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:25 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 594 expanded)
%              Number of leaves         :   17 ( 187 expanded)
%              Depth                    :   30
%              Number of atoms          :  663 (3819 expanded)
%              Number of equality atoms :   66 ( 564 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f278,f287])).

fof(f287,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f280,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f93,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f93,plain,(
    ~ v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

% (13072)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f92,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f41])).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f44])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f45,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f276,f196])).

fof(f196,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f126,f190])).

fof(f190,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f189,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f189,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ r1_tarski(k1_xboole_0,sK4(k4_orders_2(sK0,sK1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f188,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,
    ( r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f187,f46])).

fof(f46,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f187,plain,
    ( r1_tarski(sK4(k4_orders_2(sK0,sK1)),k3_tarski(k4_orders_2(sK0,sK1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f131,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f131,plain,
    ( r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f103,f126])).

fof(f103,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f102,f40])).

fof(f102,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f43])).

fof(f99,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X3] :
      ( ~ m2_orders_2(X3,sK0,sK1)
      | r2_hidden(X3,k4_orders_2(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f70])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X4,X0,X1)
      | r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f126,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_2
  <=> m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f276,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f228,f45])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f227,f40])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f226,f41])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f225,f42])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f224,f43])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f223,f44])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f218,f195])).

fof(f195,plain,
    ( v6_orders_2(k1_xboole_0,sK0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f129,f190])).

fof(f129,plain,
    ( v6_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f126,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f43])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v6_orders_2(X0,sK0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f194,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( sK2(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK2(X0,X1,X2))))
                    & r2_hidden(sK2(X0,X1,X2),X2)
                    & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK2(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK2(X0,X1,X2))))
        & r2_hidden(sK2(X0,X1,X2),X2)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f194,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f128,f190])).

fof(f128,plain,
    ( m1_subset_1(sK4(k4_orders_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f126,f88])).

fof(f88,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f127,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f118,f124,f120])).

fof(f118,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | k1_xboole_0 = k4_orders_2(sK0,sK1) ),
    inference(resolution,[],[f98,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f98,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f97,f40])).

fof(f97,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f41])).

fof(f96,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f95,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f77,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_orders_2(sK0,sK1))
      | m2_orders_2(X2,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | m2_orders_2(X4,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1233223682)
% 0.13/0.39  ipcrm: permission denied for id (1233289241)
% 0.21/0.49  ipcrm: permission denied for id (1233551461)
% 0.21/0.61  % (13086)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.62  % (13068)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.62  % (13068)Refutation not found, incomplete strategy% (13068)------------------------------
% 0.21/0.62  % (13068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (13068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (13068)Memory used [KB]: 10618
% 0.21/0.62  % (13068)Time elapsed: 0.078 s
% 0.21/0.62  % (13068)------------------------------
% 0.21/0.62  % (13068)------------------------------
% 0.21/0.62  % (13069)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.63  % (13078)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.12/0.63  % (13079)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.12/0.64  % (13069)Refutation found. Thanks to Tanya!
% 1.12/0.64  % SZS status Theorem for theBenchmark
% 1.12/0.64  % SZS output start Proof for theBenchmark
% 1.12/0.64  fof(f289,plain,(
% 1.12/0.64    $false),
% 1.12/0.64    inference(avatar_sat_refutation,[],[f127,f278,f287])).
% 1.12/0.64  fof(f287,plain,(
% 1.12/0.64    ~spl5_1),
% 1.12/0.64    inference(avatar_contradiction_clause,[],[f286])).
% 1.12/0.64  fof(f286,plain,(
% 1.12/0.64    $false | ~spl5_1),
% 1.12/0.64    inference(subsumption_resolution,[],[f280,f47])).
% 1.12/0.64  fof(f47,plain,(
% 1.12/0.64    v1_xboole_0(k1_xboole_0)),
% 1.12/0.64    inference(cnf_transformation,[],[f1])).
% 1.12/0.64  fof(f1,axiom,(
% 1.12/0.64    v1_xboole_0(k1_xboole_0)),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.12/0.64  fof(f280,plain,(
% 1.12/0.64    ~v1_xboole_0(k1_xboole_0) | ~spl5_1),
% 1.12/0.64    inference(backward_demodulation,[],[f93,f122])).
% 1.12/0.64  fof(f122,plain,(
% 1.12/0.64    k1_xboole_0 = k4_orders_2(sK0,sK1) | ~spl5_1),
% 1.12/0.64    inference(avatar_component_clause,[],[f120])).
% 1.12/0.64  fof(f120,plain,(
% 1.12/0.64    spl5_1 <=> k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 1.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.12/0.64  fof(f93,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1))),
% 1.12/0.64    inference(subsumption_resolution,[],[f92,f40])).
% 1.12/0.64  fof(f40,plain,(
% 1.12/0.64    ~v2_struct_0(sK0)),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f26,plain,(
% 1.12/0.64    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 1.12/0.64  fof(f24,plain,(
% 1.12/0.64    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.12/0.64    introduced(choice_axiom,[])).
% 1.12/0.64  fof(f25,plain,(
% 1.12/0.64    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.12/0.64    introduced(choice_axiom,[])).
% 1.12/0.64  fof(f13,plain,(
% 1.12/0.64    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f12])).
% 1.12/0.64  % (13072)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.12/0.64  fof(f12,plain,(
% 1.12/0.64    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.12/0.64    inference(ennf_transformation,[],[f11])).
% 1.12/0.64  fof(f11,negated_conjecture,(
% 1.12/0.64    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.12/0.64    inference(negated_conjecture,[],[f10])).
% 1.12/0.64  fof(f10,conjecture,(
% 1.12/0.64    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 1.12/0.64  fof(f92,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | v2_struct_0(sK0)),
% 1.12/0.64    inference(subsumption_resolution,[],[f91,f41])).
% 1.12/0.64  fof(f41,plain,(
% 1.12/0.64    v3_orders_2(sK0)),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f91,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.12/0.64    inference(subsumption_resolution,[],[f90,f42])).
% 1.12/0.64  fof(f42,plain,(
% 1.12/0.64    v4_orders_2(sK0)),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f90,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.12/0.64    inference(subsumption_resolution,[],[f89,f43])).
% 1.12/0.64  fof(f43,plain,(
% 1.12/0.64    v5_orders_2(sK0)),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f89,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.12/0.64    inference(subsumption_resolution,[],[f76,f44])).
% 1.12/0.64  fof(f44,plain,(
% 1.12/0.64    l1_orders_2(sK0)),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f76,plain,(
% 1.12/0.64    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.12/0.64    inference(resolution,[],[f45,f63])).
% 1.12/0.64  fof(f63,plain,(
% 1.12/0.64    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v1_xboole_0(k4_orders_2(X0,X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f21])).
% 1.12/0.64  fof(f21,plain,(
% 1.12/0.64    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f20])).
% 1.12/0.64  fof(f20,plain,(
% 1.12/0.64    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.12/0.64    inference(ennf_transformation,[],[f9])).
% 1.12/0.64  fof(f9,axiom,(
% 1.12/0.64    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 1.12/0.64  fof(f45,plain,(
% 1.12/0.64    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f278,plain,(
% 1.12/0.64    ~spl5_2),
% 1.12/0.64    inference(avatar_contradiction_clause,[],[f277])).
% 1.12/0.64  fof(f277,plain,(
% 1.12/0.64    $false | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f276,f196])).
% 1.12/0.64  fof(f196,plain,(
% 1.12/0.64    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_2),
% 1.12/0.64    inference(backward_demodulation,[],[f126,f190])).
% 1.12/0.64  fof(f190,plain,(
% 1.12/0.64    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f189,f48])).
% 1.12/0.64  fof(f48,plain,(
% 1.12/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f3])).
% 1.12/0.64  fof(f3,axiom,(
% 1.12/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.12/0.64  fof(f189,plain,(
% 1.12/0.64    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | ~r1_tarski(k1_xboole_0,sK4(k4_orders_2(sK0,sK1))) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f188,f68])).
% 1.12/0.64  fof(f68,plain,(
% 1.12/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f39])).
% 1.12/0.64  fof(f39,plain,(
% 1.12/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.12/0.64    inference(flattening,[],[f38])).
% 1.12/0.64  fof(f38,plain,(
% 1.12/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.12/0.64    inference(nnf_transformation,[],[f2])).
% 1.12/0.64  fof(f2,axiom,(
% 1.12/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.12/0.64  fof(f188,plain,(
% 1.12/0.64    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k1_xboole_0) | ~spl5_2),
% 1.12/0.64    inference(forward_demodulation,[],[f187,f46])).
% 1.12/0.64  fof(f46,plain,(
% 1.12/0.64    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 1.12/0.64    inference(cnf_transformation,[],[f26])).
% 1.12/0.64  fof(f187,plain,(
% 1.12/0.64    r1_tarski(sK4(k4_orders_2(sK0,sK1)),k3_tarski(k4_orders_2(sK0,sK1))) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f131,f62])).
% 1.12/0.64  fof(f62,plain,(
% 1.12/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.12/0.64    inference(cnf_transformation,[],[f19])).
% 1.12/0.64  fof(f19,plain,(
% 1.12/0.64    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.12/0.64    inference(ennf_transformation,[],[f4])).
% 1.12/0.64  fof(f4,axiom,(
% 1.12/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.12/0.64  fof(f131,plain,(
% 1.12/0.64    r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1)) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f103,f126])).
% 1.12/0.64  fof(f103,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1))) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f102,f40])).
% 1.12/0.64  fof(f102,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1)) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f101,f41])).
% 1.12/0.64  fof(f101,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f100,f42])).
% 1.12/0.64  fof(f100,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f99,f43])).
% 1.12/0.64  fof(f99,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f78,f44])).
% 1.12/0.64  fof(f78,plain,(
% 1.12/0.64    ( ! [X3] : (~m2_orders_2(X3,sK0,sK1) | r2_hidden(X3,k4_orders_2(sK0,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(resolution,[],[f45,f70])).
% 1.12/0.64  fof(f70,plain,(
% 1.12/0.64    ( ! [X4,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X4,X0,X1) | r2_hidden(X4,k4_orders_2(X0,X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(equality_resolution,[],[f56])).
% 1.12/0.64  fof(f56,plain,(
% 1.12/0.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f35])).
% 1.12/0.64  fof(f35,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.12/0.64  fof(f34,plain,(
% 1.12/0.64    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.12/0.64    introduced(choice_axiom,[])).
% 1.12/0.64  fof(f33,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(rectify,[],[f32])).
% 1.12/0.64  fof(f32,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(nnf_transformation,[],[f17])).
% 1.12/0.64  fof(f17,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f16])).
% 1.12/0.64  fof(f16,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.12/0.64    inference(ennf_transformation,[],[f7])).
% 1.12/0.64  fof(f7,axiom,(
% 1.12/0.64    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 1.12/0.64  fof(f126,plain,(
% 1.12/0.64    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | ~spl5_2),
% 1.12/0.64    inference(avatar_component_clause,[],[f124])).
% 1.12/0.64  fof(f124,plain,(
% 1.12/0.64    spl5_2 <=> m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)),
% 1.12/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.12/0.64  fof(f276,plain,(
% 1.12/0.64    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f228,f45])).
% 1.12/0.64  fof(f228,plain,(
% 1.12/0.64    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f227,f40])).
% 1.12/0.64  fof(f227,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f226,f41])).
% 1.12/0.64  fof(f226,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f225,f42])).
% 1.12/0.64  fof(f225,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f224,f43])).
% 1.12/0.64  fof(f224,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f223,f44])).
% 1.12/0.64  fof(f223,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(subsumption_resolution,[],[f218,f195])).
% 1.12/0.64  fof(f195,plain,(
% 1.12/0.64    v6_orders_2(k1_xboole_0,sK0) | ~spl5_2),
% 1.12/0.64    inference(backward_demodulation,[],[f129,f190])).
% 1.12/0.64  fof(f129,plain,(
% 1.12/0.64    v6_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f126,f83])).
% 1.12/0.64  fof(f83,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f82,f40])).
% 1.12/0.64  fof(f82,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f81,f41])).
% 1.12/0.64  fof(f81,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f80,f42])).
% 1.12/0.64  fof(f80,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f79,f43])).
% 1.12/0.64  fof(f79,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f74,f44])).
% 1.12/0.64  fof(f74,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v6_orders_2(X0,sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(resolution,[],[f45,f64])).
% 1.12/0.64  fof(f64,plain,(
% 1.12/0.64    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f23])).
% 1.12/0.64  fof(f23,plain,(
% 1.12/0.64    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f22])).
% 1.12/0.64  fof(f22,plain,(
% 1.12/0.64    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.12/0.64    inference(ennf_transformation,[],[f8])).
% 1.12/0.64  fof(f8,axiom,(
% 1.12/0.64    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.12/0.64  fof(f218,plain,(
% 1.12/0.64    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f194,f69])).
% 1.12/0.64  fof(f69,plain,(
% 1.12/0.64    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(equality_resolution,[],[f49])).
% 1.12/0.64  fof(f49,plain,(
% 1.12/0.64    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f31])).
% 1.12/0.64  fof(f31,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (sK2(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK2(X0,X1,X2)))) & r2_hidden(sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.12/0.64  fof(f30,plain,(
% 1.12/0.64    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (sK2(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK2(X0,X1,X2)))) & r2_hidden(sK2(X0,X1,X2),X2) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.12/0.64    introduced(choice_axiom,[])).
% 1.12/0.64  fof(f29,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(rectify,[],[f28])).
% 1.12/0.64  fof(f28,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f27])).
% 1.12/0.64  fof(f27,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(nnf_transformation,[],[f15])).
% 1.12/0.64  fof(f15,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.12/0.64    inference(flattening,[],[f14])).
% 1.12/0.64  fof(f14,plain,(
% 1.12/0.64    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.12/0.64    inference(ennf_transformation,[],[f6])).
% 1.12/0.64  fof(f6,axiom,(
% 1.12/0.64    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 1.12/0.64  fof(f194,plain,(
% 1.12/0.64    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 1.12/0.64    inference(backward_demodulation,[],[f128,f190])).
% 1.12/0.64  fof(f128,plain,(
% 1.12/0.64    m1_subset_1(sK4(k4_orders_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 1.12/0.64    inference(resolution,[],[f126,f88])).
% 1.12/0.64  fof(f88,plain,(
% 1.12/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f87,f40])).
% 1.12/0.64  fof(f87,plain,(
% 1.12/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.12/0.64    inference(subsumption_resolution,[],[f86,f41])).
% 1.22/0.64  fof(f86,plain,(
% 1.22/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f85,f42])).
% 1.22/0.64  fof(f85,plain,(
% 1.22/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f84,f43])).
% 1.22/0.64  fof(f84,plain,(
% 1.22/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f75,f44])).
% 1.22/0.64  fof(f75,plain,(
% 1.22/0.64    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(resolution,[],[f45,f65])).
% 1.22/0.64  fof(f65,plain,(
% 1.22/0.64    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.22/0.64    inference(cnf_transformation,[],[f23])).
% 1.22/0.64  fof(f127,plain,(
% 1.22/0.64    spl5_1 | spl5_2),
% 1.22/0.64    inference(avatar_split_clause,[],[f118,f124,f120])).
% 1.22/0.64  fof(f118,plain,(
% 1.22/0.64    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | k1_xboole_0 = k4_orders_2(sK0,sK1)),
% 1.22/0.64    inference(resolution,[],[f98,f59])).
% 1.22/0.64  fof(f59,plain,(
% 1.22/0.64    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.22/0.64    inference(cnf_transformation,[],[f37])).
% 1.22/0.64  fof(f37,plain,(
% 1.22/0.64    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 1.22/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f36])).
% 1.22/0.64  fof(f36,plain,(
% 1.22/0.64    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 1.22/0.64    introduced(choice_axiom,[])).
% 1.22/0.64  fof(f18,plain,(
% 1.22/0.64    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.22/0.64    inference(ennf_transformation,[],[f5])).
% 1.22/0.64  fof(f5,axiom,(
% 1.22/0.64    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.22/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.22/0.64  fof(f98,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f97,f40])).
% 1.22/0.64  fof(f97,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f96,f41])).
% 1.22/0.64  fof(f96,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f95,f42])).
% 1.22/0.64  fof(f95,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f94,f43])).
% 1.22/0.64  fof(f94,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(subsumption_resolution,[],[f77,f44])).
% 1.22/0.64  fof(f77,plain,(
% 1.22/0.64    ( ! [X2] : (~r2_hidden(X2,k4_orders_2(sK0,sK1)) | m2_orders_2(X2,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.22/0.64    inference(resolution,[],[f45,f71])).
% 1.22/0.64  fof(f71,plain,(
% 1.22/0.64    ( ! [X4,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | m2_orders_2(X4,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.22/0.64    inference(equality_resolution,[],[f55])).
% 1.22/0.64  fof(f55,plain,(
% 1.22/0.64    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.22/0.64    inference(cnf_transformation,[],[f35])).
% 1.22/0.64  % SZS output end Proof for theBenchmark
% 1.22/0.64  % (13069)------------------------------
% 1.22/0.64  % (13069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.64  % (13069)Termination reason: Refutation
% 1.22/0.64  
% 1.22/0.64  % (13069)Memory used [KB]: 10746
% 1.22/0.64  % (13069)Time elapsed: 0.099 s
% 1.22/0.64  % (13069)------------------------------
% 1.22/0.64  % (13069)------------------------------
% 1.22/0.64  % (13075)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.22/0.65  % (13071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.28/0.65  % (13087)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.28/0.65  % (12908)Success in time 0.294 s
%------------------------------------------------------------------------------
