%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  88 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 397 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f47,f51,f67,f131])).

fof(f131,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f129,f66])).

fof(f66,plain,
    ( ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_7
  <=> r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f129,plain,
    ( r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,
    ( r3_lattice3(sK0,sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_5
  <=> r3_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f72,f28])).

fof(f28,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f71,f40])).

fof(f40,plain,
    ( l3_lattices(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f70,f36])).

fof(f36,plain,
    ( v4_lattice3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f68,f32])).

fof(f32,plain,
    ( v10_lattices(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl4_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,X1)
        | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) )
    | spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f43,plain,
    ( ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f42,f28])).

fof(f42,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f67,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f12,f65])).

fof(f12,plain,(
    ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(f51,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f13,f49])).

fof(f13,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f11,f45])).

fof(f11,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (10689)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (10689)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (10696)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f47,f51,f67,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_7 <=> r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl4_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.48    inference(resolution,[],[f73,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r3_lattice3(sK0,sK1,sK2) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_5 <=> r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    l3_lattices(sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl4_4 <=> l3_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v4_lattice3(sK0) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    spl4_3 <=> v4_lattice3(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v10_lattices(sK0) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl4_2 <=> v10_lattices(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))) ) | (spl4_1 | ~spl4_4)),
% 0.21/0.48    inference(resolution,[],[f43,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f42,f28])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | ~spl4_4),
% 0.21/0.48    inference(resolution,[],[f40,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f12,f65])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f49])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f45])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    l3_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f35])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    v4_lattice3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v10_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10689)------------------------------
% 0.21/0.48  % (10689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10689)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10689)Memory used [KB]: 6140
% 0.21/0.48  % (10689)Time elapsed: 0.063 s
% 0.21/0.48  % (10689)------------------------------
% 0.21/0.48  % (10689)------------------------------
% 0.21/0.49  % (10688)Success in time 0.125 s
%------------------------------------------------------------------------------
