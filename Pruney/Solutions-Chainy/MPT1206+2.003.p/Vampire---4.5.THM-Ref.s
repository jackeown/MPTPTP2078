%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 118 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 ( 514 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f63,f68,f72,f80])).

fof(f80,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f78,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(f78,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f77,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f76,f46])).

fof(f46,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f75,f23])).

fof(f23,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,
    ( ~ v13_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f74,f50])).

fof(f50,plain,
    ( l1_lattices(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_2
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_4 ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl3_4 ),
    inference(superposition,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f59,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_4
  <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f70,f21])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f69,f50])).

fof(f69,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_1 ),
    inference(resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f47,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f66,f24])).

fof(f24,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,
    ( ~ l3_lattices(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f65,f22])).

fof(f22,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f64,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_3 ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f55,plain,
    ( ~ v6_lattices(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_3
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f61,plain,
    ( ~ l3_lattices(sK0)
    | spl3_2 ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f51,plain,
    ( ~ l1_lattices(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f60,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f43,f57,f53,f49,f45])).

fof(f43,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f42,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f41,f19])).

fof(f41,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f20,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f20,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:52:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (16637)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (16642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (16638)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16637)Refutation not found, incomplete strategy% (16637)------------------------------
% 0.20/0.49  % (16637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16637)Memory used [KB]: 6140
% 0.20/0.49  % (16637)Time elapsed: 0.071 s
% 0.20/0.49  % (16637)------------------------------
% 0.20/0.49  % (16637)------------------------------
% 0.20/0.49  % (16652)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (16638)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (16641)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (16646)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f60,f63,f68,f72,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | spl3_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | spl3_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    v2_struct_0(sK0) | (~spl3_1 | ~spl3_2 | spl3_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_1 | ~spl3_2 | spl3_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f76,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl3_1 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | spl3_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    v13_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~v13_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | spl3_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    l1_lattices(sK0) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl3_2 <=> l1_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~l1_lattices(sK0) | ~v13_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_4),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    k5_lattices(sK0) != k5_lattices(sK0) | ~l1_lattices(sK0) | ~v13_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | spl3_4),
% 0.20/0.49    inference(superposition,[],[f59,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | k5_lattices(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1) | spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl3_4 <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f70,f21])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    v2_struct_0(sK0) | (spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f50])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f47,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    $false | spl3_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f66,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    l3_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | spl3_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f65,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    v10_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl3_3),
% 0.20/0.49    inference(subsumption_resolution,[],[f64,f21])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl3_3),
% 0.20/0.49    inference(resolution,[],[f55,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ~v6_lattices(sK0) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl3_3 <=> v6_lattices(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    $false | spl3_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f61,f24])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | spl3_2),
% 0.20/0.50    inference(resolution,[],[f51,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ~l1_lattices(sK0) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f49])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f43,f57,f53,f49,f45])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f42,f21])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f41,f19])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK1) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.20/0.50    inference(superposition,[],[f20,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16638)------------------------------
% 0.20/0.50  % (16638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16638)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16638)Memory used [KB]: 10618
% 0.20/0.50  % (16638)Time elapsed: 0.072 s
% 0.20/0.50  % (16638)------------------------------
% 0.20/0.50  % (16638)------------------------------
% 0.20/0.50  % (16639)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (16636)Success in time 0.134 s
%------------------------------------------------------------------------------
