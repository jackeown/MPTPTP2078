%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:55 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 115 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  238 ( 468 expanded)
%              Number of equality atoms :    7 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f56,f61,f70,f82,f88])).

fof(f88,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f86,f50])).

fof(f50,plain,
    ( v5_funct_1(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_5
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( ~ v5_funct_1(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f85,f69])).

fof(f69,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_8
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f85,plain,
    ( ~ r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v5_funct_1(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f83,f35])).

fof(f35,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v5_funct_1(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(resolution,[],[f81,f30])).

fof(f30,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f82,plain,
    ( spl4_9
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f78,f58,f53,f38,f80])).

fof(f38,plain,
    ( spl4_3
  <=> v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f53,plain,
    ( spl4_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f58,plain,
    ( spl4_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1) )
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f77,f55])).

fof(f55,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1) )
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f74,f60])).

fof(f60,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(sK2(sK1),k1_relat_1(X0))
        | ~ v5_funct_1(X0,sK1) )
    | spl4_3 ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,
    ( ~ v2_relat_1(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(sK2(X0),k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(sK2(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v5_funct_1(X1,X0) ) ),
    inference(resolution,[],[f71,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_funct_1(X0,sK2(X0)))
      | ~ v1_relat_1(X0)
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

fof(f70,plain,
    ( spl4_8
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f65,f58,f53,f43,f38,f67])).

fof(f43,plain,
    ( spl4_4
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f65,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f64,f40])).

fof(f64,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | v2_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f63,f60])).

fof(f63,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | v2_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f62,f55])).

fof(f62,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_relat_1(sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f21,f45])).

fof(f45,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f13,f58])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

fof(f56,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f14,f53])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f15,f48])).

fof(f15,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f28])).

fof(f19,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (23320)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.41  % (23330)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.13/0.41  % (23320)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f97,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f56,f61,f70,f82,f88])).
% 0.13/0.42  fof(f88,plain,(
% 0.13/0.42    ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_8 | ~spl4_9),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f87])).
% 0.13/0.42  fof(f87,plain,(
% 0.13/0.42    $false | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_8 | ~spl4_9)),
% 0.13/0.42    inference(subsumption_resolution,[],[f86,f50])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    v5_funct_1(sK0,sK1) | ~spl4_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f48])).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    spl4_5 <=> v5_funct_1(sK0,sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.13/0.42  fof(f86,plain,(
% 0.13/0.42    ~v5_funct_1(sK0,sK1) | (~spl4_1 | ~spl4_2 | ~spl4_8 | ~spl4_9)),
% 0.13/0.42    inference(subsumption_resolution,[],[f85,f69])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~spl4_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f67])).
% 0.13/0.42  fof(f67,plain,(
% 0.13/0.42    spl4_8 <=> r2_hidden(sK2(sK1),k1_relat_1(sK0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.13/0.42  fof(f85,plain,(
% 0.13/0.42    ~r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v5_funct_1(sK0,sK1) | (~spl4_1 | ~spl4_2 | ~spl4_9)),
% 0.13/0.42    inference(subsumption_resolution,[],[f83,f35])).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    v1_relat_1(sK0) | ~spl4_2),
% 0.13/0.42    inference(avatar_component_clause,[],[f33])).
% 0.13/0.42  fof(f33,plain,(
% 0.13/0.42    spl4_2 <=> v1_relat_1(sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.13/0.42  fof(f83,plain,(
% 0.13/0.42    ~v1_relat_1(sK0) | ~r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v5_funct_1(sK0,sK1) | (~spl4_1 | ~spl4_9)),
% 0.13/0.42    inference(resolution,[],[f81,f30])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    v1_funct_1(sK0) | ~spl4_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f28])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    spl4_1 <=> v1_funct_1(sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.13/0.42  fof(f81,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1)) ) | ~spl4_9),
% 0.13/0.42    inference(avatar_component_clause,[],[f80])).
% 0.13/0.42  fof(f80,plain,(
% 0.13/0.42    spl4_9 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.13/0.42  fof(f82,plain,(
% 0.13/0.42    spl4_9 | spl4_3 | ~spl4_6 | ~spl4_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f78,f58,f53,f38,f80])).
% 0.13/0.42  fof(f38,plain,(
% 0.13/0.42    spl4_3 <=> v2_relat_1(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    spl4_6 <=> v1_funct_1(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.13/0.42  fof(f58,plain,(
% 0.13/0.42    spl4_7 <=> v1_relat_1(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.13/0.42  fof(f78,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1)) ) | (spl4_3 | ~spl4_6 | ~spl4_7)),
% 0.13/0.42    inference(subsumption_resolution,[],[f77,f55])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    v1_funct_1(sK1) | ~spl4_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f53])).
% 0.13/0.42  fof(f77,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1)) ) | (spl4_3 | ~spl4_7)),
% 0.13/0.42    inference(subsumption_resolution,[],[f74,f60])).
% 0.13/0.42  fof(f60,plain,(
% 0.13/0.42    v1_relat_1(sK1) | ~spl4_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f58])).
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(sK2(sK1),k1_relat_1(X0)) | ~v5_funct_1(X0,sK1)) ) | spl4_3),
% 0.13/0.42    inference(resolution,[],[f73,f40])).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    ~v2_relat_1(sK1) | spl4_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f38])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    ( ! [X0,X1] : (v2_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(sK2(X0),k1_relat_1(X1)) | ~v5_funct_1(X1,X0)) )),
% 0.13/0.42    inference(duplicate_literal_removal,[],[f72])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(sK2(X0),k1_relat_1(X1)) | ~v1_relat_1(X0) | ~v5_funct_1(X1,X0)) )),
% 0.13/0.42    inference(resolution,[],[f71,f23])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X0) | ~v5_funct_1(X1,X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r2_hidden(X1,k1_funct_1(X0,sK2(X0))) | ~v1_relat_1(X0) | v2_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.13/0.42    inference(resolution,[],[f22,f26])).
% 0.13/0.42  fof(f26,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ( ! [X0] : (v1_xboole_0(k1_funct_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f9])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f8])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    spl4_8 | spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f65,f58,f53,f43,f38,f67])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    spl4_4 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | (spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.13/0.42    inference(subsumption_resolution,[],[f64,f40])).
% 0.13/0.42  fof(f64,plain,(
% 0.13/0.42    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | v2_relat_1(sK1) | (~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.13/0.42    inference(subsumption_resolution,[],[f63,f60])).
% 0.13/0.42  fof(f63,plain,(
% 0.13/0.42    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | v2_relat_1(sK1) | (~spl4_4 | ~spl4_6)),
% 0.13/0.42    inference(subsumption_resolution,[],[f62,f55])).
% 0.13/0.42  fof(f62,plain,(
% 0.13/0.42    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_relat_1(sK1) | ~spl4_4),
% 0.13/0.42    inference(superposition,[],[f21,f45])).
% 0.13/0.42  fof(f45,plain,(
% 0.13/0.42    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl4_4),
% 0.13/0.42    inference(avatar_component_clause,[],[f43])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f9])).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    spl4_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f13,f58])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    v1_relat_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,plain,(
% 0.13/0.42    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f6])).
% 0.13/0.42  fof(f6,plain,(
% 0.13/0.42    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,negated_conjecture,(
% 0.13/0.42    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.13/0.42    inference(negated_conjecture,[],[f4])).
% 0.13/0.42  fof(f4,conjecture,(
% 0.13/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).
% 0.13/0.42  fof(f56,plain,(
% 0.13/0.42    spl4_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f14,f53])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    v1_funct_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    spl4_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f15,f48])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    v5_funct_1(sK0,sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    spl4_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f16,f43])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f41,plain,(
% 0.13/0.42    ~spl4_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f17,f38])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    ~v2_relat_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    spl4_2),
% 0.13/0.42    inference(avatar_split_clause,[],[f18,f33])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    v1_relat_1(sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  fof(f31,plain,(
% 0.13/0.42    spl4_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f28])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    v1_funct_1(sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f7])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (23320)------------------------------
% 0.13/0.42  % (23320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (23320)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (23320)Memory used [KB]: 10618
% 0.13/0.42  % (23320)Time elapsed: 0.006 s
% 0.13/0.42  % (23320)------------------------------
% 0.13/0.42  % (23320)------------------------------
% 0.21/0.42  % (23318)Success in time 0.064 s
%------------------------------------------------------------------------------
