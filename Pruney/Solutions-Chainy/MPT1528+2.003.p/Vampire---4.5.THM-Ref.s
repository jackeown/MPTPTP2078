%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  83 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 331 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f52,f58])).

fof(f58,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f56,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f56,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | spl4_1 ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,X0,sK1)
      | r2_hidden(sK3(sK0,X0,sK1),X0) ) ),
    inference(resolution,[],[f53,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
            | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
          | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X0)
      | r2_lattice3(sK0,X0,X1) ) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_2 ),
    inference(resolution,[],[f49,f37])).

fof(f49,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | spl4_2 ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> r1_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f48,plain,(
    ! [X0] :
      ( r1_lattice3(sK0,X0,sK1)
      | r2_hidden(sK2(sK0,X0,sK1),X0) ) ),
    inference(resolution,[],[f47,f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK2(sK0,X0,X1),X0)
      | r1_lattice3(sK0,X0,X1) ) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f46,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f43,f39])).

fof(f27,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:09:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (23914)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.46  % (23917)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.47  % (23910)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (23910)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f46,f52,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    $false | spl4_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f56,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl4_1),
% 0.20/0.47    inference(resolution,[],[f55,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0) | spl4_1),
% 0.20/0.47    inference(resolution,[],[f54,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ~r2_lattice3(sK0,k1_xboole_0,sK1) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl4_1 <=> r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (r2_lattice3(sK0,X0,sK1) | r2_hidden(sK3(sK0,X0,sK1),X0)) )),
% 0.20/0.47    inference(resolution,[],[f53,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f35,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    l1_orders_2(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(rectify,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    $false | spl4_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f28])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | spl4_2),
% 0.20/0.47    inference(resolution,[],[f49,f37])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0) | spl4_2),
% 0.20/0.47    inference(resolution,[],[f48,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ~r1_lattice3(sK0,k1_xboole_0,sK1) | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl4_2 <=> r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (r1_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)) )),
% 0.20/0.47    inference(resolution,[],[f47,f26])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f31,f25])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(rectify,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f27,f43,f39])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (23910)------------------------------
% 0.20/0.47  % (23910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23910)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (23910)Memory used [KB]: 5373
% 0.20/0.47  % (23910)Time elapsed: 0.052 s
% 0.20/0.47  % (23910)------------------------------
% 0.20/0.47  % (23910)------------------------------
% 0.20/0.48  % (23907)Success in time 0.115 s
%------------------------------------------------------------------------------
