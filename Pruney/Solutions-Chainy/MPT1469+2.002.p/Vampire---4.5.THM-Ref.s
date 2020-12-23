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
% DateTime   : Thu Dec  3 13:15:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 120 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 334 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f41,f72,f77,f81,f86,f90,f95,f121])).

fof(f121,plain,
    ( spl3_2
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f115,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f115,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f28,f112])).

fof(f112,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f56,f94])).

fof(f94,plain,
    ( sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_7
  <=> sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f56,plain,(
    k2_xboole_0(sK1,sK2) = k1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(resolution,[],[f44,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
           => ( r1_lattices(k1_lattice3(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).

fof(f44,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0)))
      | k1_lattices(k1_lattice3(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f30,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_lattice3)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f95,plain,
    ( spl3_3
    | spl3_7
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f91,f33,f70,f67,f64,f93,f61])).

fof(f61,plain,
    ( spl3_3
  <=> v2_struct_0(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_6
  <=> l2_lattices(k1_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f33,plain,
    ( spl3_1
  <=> r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f91,plain,
    ( ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f39,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f90,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f62,f23])).

fof(f23,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f62,plain,
    ( v2_struct_0(k1_lattice3(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f68,f22])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f65,f21])).

fof(f65,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f73,f24])).

fof(f24,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f73,plain,
    ( ~ l3_lattices(k1_lattice3(sK0))
    | spl3_6 ),
    inference(resolution,[],[f71,f25])).

fof(f25,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f71,plain,
    ( ~ l2_lattices(k1_lattice3(sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,
    ( spl3_1
    | spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f36,f70,f67,f64,f61,f33])).

fof(f59,plain,
    ( ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | v2_struct_0(k1_lattice3(sK0))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( sK2 != sK2
    | ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | v2_struct_0(k1_lattice3(sK0))
    | r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f26,f57])).

fof(f57,plain,
    ( sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f56,f42])).

fof(f42,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f19,f36,f33])).

fof(f19,plain,
    ( r1_tarski(sK1,sK2)
    | r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f36,f33])).

fof(f20,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n007.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:02:36 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.43  % (18005)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.44  % (18001)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.44  % (18021)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.44  % (18013)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.45  % (18013)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (18021)Refutation not found, incomplete strategy% (18021)------------------------------
% 0.20/0.46  % (18021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (18021)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (18021)Memory used [KB]: 6140
% 0.20/0.46  % (18021)Time elapsed: 0.077 s
% 0.20/0.46  % (18021)------------------------------
% 0.20/0.46  % (18021)------------------------------
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f38,f41,f72,f77,f81,f86,f90,f95,f121])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl3_2 | ~spl3_7),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    $false | (spl3_2 | ~spl3_7)),
% 0.20/0.46    inference(resolution,[],[f115,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ~r1_tarski(sK1,sK2) | spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    r1_tarski(sK1,sK2) | ~spl3_7),
% 0.20/0.46    inference(superposition,[],[f28,f112])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_7),
% 0.20/0.46    inference(forward_demodulation,[],[f56,f94])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl3_7 <=> sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    k2_xboole_0(sK1,sK2) = k1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.46    inference(resolution,[],[f44,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_lattice3)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k1_lattice3(sK0))) | k1_lattices(k1_lattice3(sK0),X0,sK2) = k2_xboole_0(X0,sK2)) )),
% 0.20/0.46    inference(resolution,[],[f30,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) | k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : ((k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_lattice3)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    spl3_3 | spl3_7 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f91,f33,f70,f67,f64,f93,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_3 <=> v2_struct_0(k1_lattice3(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl3_4 <=> m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl3_6 <=> l2_lattices(k1_lattice3(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl3_1 <=> r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | v2_struct_0(k1_lattice3(sK0)) | ~spl3_1),
% 0.20/0.46    inference(resolution,[],[f39,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ~spl3_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    $false | ~spl3_3),
% 0.20/0.46    inference(resolution,[],[f62,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    v2_struct_0(k1_lattice3(sK0)) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    $false | spl3_5),
% 0.20/0.46    inference(resolution,[],[f68,f22])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    $false | spl3_4),
% 0.20/0.46    inference(resolution,[],[f65,f21])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f64])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    spl3_6),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    $false | spl3_6),
% 0.20/0.46    inference(resolution,[],[f73,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ~l3_lattices(k1_lattice3(sK0)) | spl3_6),
% 0.20/0.46    inference(resolution,[],[f71,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.20/0.46    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~l2_lattices(k1_lattice3(sK0)) | spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f70])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl3_1 | spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f59,f36,f70,f67,f64,f61,f33])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | v2_struct_0(k1_lattice3(sK0)) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_2),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    sK2 != sK2 | ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | v2_struct_0(k1_lattice3(sK0)) | r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_2),
% 0.20/0.46    inference(superposition,[],[f26,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~spl3_2),
% 0.20/0.46    inference(forward_demodulation,[],[f56,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.20/0.46    inference(resolution,[],[f29,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r1_lattices(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl3_1 | spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f36,f33])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ~spl3_1 | ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f36,f33])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ~r1_tarski(sK1,sK2) | ~r1_lattices(k1_lattice3(sK0),sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (18013)------------------------------
% 0.20/0.46  % (18013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (18013)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (18013)Memory used [KB]: 10618
% 0.20/0.46  % (18013)Time elapsed: 0.083 s
% 0.20/0.46  % (18013)------------------------------
% 0.20/0.46  % (18013)------------------------------
% 0.20/0.46  % (18000)Success in time 0.118 s
%------------------------------------------------------------------------------
