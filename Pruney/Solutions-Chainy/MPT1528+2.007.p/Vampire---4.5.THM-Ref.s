%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  58 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f40,f46])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f44,f33])).

fof(f33,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_2
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44,plain,(
    r2_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f43,f16])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r2_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0,sK1),X0)
      | r2_lattice3(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f41,f15])).

fof(f15,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK3(sK0,X0,sK1),X0)
      | r2_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f23,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f40,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f38,f29])).

fof(f29,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_1
  <=> r1_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f38,plain,(
    r1_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(resolution,[],[f37,f16])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r1_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0,sK1),X0)
      | r1_lattice3(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f35,f15])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | r2_hidden(sK2(sK0,X0,sK1),X0)
      | r1_lattice3(sK0,X0,sK1) ) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f34,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f31,f27])).

fof(f13,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ r1_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:27:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (1106)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (1106)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f34,f40,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    $false | spl4_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~r2_lattice3(sK0,k1_xboole_0,sK1) | spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    spl4_2 <=> r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.21/0.47    inference(resolution,[],[f43,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | r2_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f42,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f41,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    l1_orders_2(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_orders_2(sK0) | r2_hidden(sK3(sK0,X0,sK1),X0) | r2_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f23,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl4_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    $false | spl4_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f38,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~r1_lattice3(sK0,k1_xboole_0,sK1) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    spl4_1 <=> r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.21/0.47    inference(resolution,[],[f37,f16])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | r1_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f36,f25])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f35,f15])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_orders_2(sK0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f19,f14])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ~spl4_1 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f31,f27])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ~r2_lattice3(sK0,k1_xboole_0,sK1) | ~r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (1106)------------------------------
% 0.21/0.47  % (1106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1106)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (1106)Memory used [KB]: 5373
% 0.21/0.47  % (1106)Time elapsed: 0.052 s
% 0.21/0.47  % (1106)------------------------------
% 0.21/0.47  % (1106)------------------------------
% 0.21/0.48  % (1097)Success in time 0.113 s
%------------------------------------------------------------------------------
