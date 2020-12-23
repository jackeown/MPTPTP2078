%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 130 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  237 ( 705 expanded)
%              Number of equality atoms :   87 ( 303 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f58,f63,f69,f75,f81])).

fof(f81,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f37,f42,f47,f52,f57,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(X0) != k1_mcart_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f57,plain,
    ( k2_mcart_1(sK1) = k2_mcart_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_7
  <=> k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f52,plain,
    ( k1_mcart_1(sK1) = k1_mcart_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_6
  <=> k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f42,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f75,plain,
    ( spl3_10
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f71,f67,f25,f73])).

fof(f25,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f70,f27])).

fof(f27,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK0)
        | k1_mcart_1(X0) != k1_mcart_1(X1)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f65,f61,f25,f67])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k2_mcart_1(X0) != k2_mcart_1(X1)
        | k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK0)
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | ~ m1_subset_1(X0,sK0) )
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl3_8 ),
    inference(resolution,[],[f62,f23])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | k2_mcart_1(X0) != k2_mcart_1(X1)
        | X0 = X1 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f30,f61])).

fof(f30,plain,
    ( spl3_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k2_mcart_1(X0) != k2_mcart_1(X1)
        | k1_mcart_1(X0) != k1_mcart_1(X1)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X0,sK0)
        | X0 = X1 )
    | ~ spl3_2 ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_mcart_1(X2) != k2_mcart_1(X0)
      | k1_mcart_1(X2) != k1_mcart_1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X0 = X2
          | k2_mcart_1(X2) != k2_mcart_1(X0)
          | k1_mcart_1(X2) != k1_mcart_1(X0)
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X2,X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( k2_mcart_1(X2) = k2_mcart_1(X0)
            & k1_mcart_1(X2) = k1_mcart_1(X0)
            & r2_hidden(X0,X1)
            & r2_hidden(X2,X1) )
         => X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    k2_mcart_1(sK1) = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != sK2
    & k2_mcart_1(sK1) = k2_mcart_1(sK2)
    & k1_mcart_1(sK1) = k1_mcart_1(sK2)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0)
    & v1_relat_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_mcart_1(X2) = k2_mcart_1(X1)
                & k1_mcart_1(X2) = k1_mcart_1(X1)
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,X0) )
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,sK0) )
      & v1_relat_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_mcart_1(X2) = k2_mcart_1(X1)
            & k1_mcart_1(X2) = k1_mcart_1(X1)
            & m1_subset_1(X2,sK0) )
        & m1_subset_1(X1,sK0) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_mcart_1(X2) = k2_mcart_1(sK1)
          & k1_mcart_1(X2) = k1_mcart_1(sK1)
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_mcart_1(X2) = k2_mcart_1(sK1)
        & k1_mcart_1(X2) = k1_mcart_1(sK1)
        & m1_subset_1(X2,sK0) )
   => ( sK1 != sK2
      & k2_mcart_1(sK1) = k2_mcart_1(sK2)
      & k1_mcart_1(sK1) = k1_mcart_1(sK2)
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_mcart_1(X2) = k2_mcart_1(X1)
              & k1_mcart_1(X2) = k1_mcart_1(X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,X0) )
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                    & k1_mcart_1(X2) = k1_mcart_1(X1) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ( k2_mcart_1(X2) = k2_mcart_1(X1)
                  & k1_mcart_1(X2) = k1_mcart_1(X1) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    k1_mcart_1(sK1) = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f25])).

fof(f15,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:24:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (31665)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.49  % (31657)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (31659)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (31655)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (31657)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f53,f58,f63,f69,f75,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    $false | (~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f37,f42,f47,f52,f57,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0) | k1_mcart_1(X0) != k1_mcart_1(X1)) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_10 <=> ! [X1,X0] : (k1_mcart_1(X0) != k1_mcart_1(X1) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    k2_mcart_1(sK1) = k2_mcart_1(sK2) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_7 <=> k2_mcart_1(sK1) = k2_mcart_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    k1_mcart_1(sK1) = k1_mcart_1(sK2) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl3_6 <=> k1_mcart_1(sK1) = k1_mcart_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    sK1 != sK2 | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_5 <=> sK1 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK2,sK0) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK1,sK0) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_10 | spl3_1 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f67,f25,f73])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    spl3_1 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_mcart_1(X0) != k1_mcart_1(X1) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | (spl3_1 | ~spl3_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f25])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_mcart_1(X0) != k1_mcart_1(X1) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(X1,sK0)) ) | ~spl3_9),
% 0.21/0.49    inference(resolution,[],[f68,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_mcart_1(X0) != k1_mcart_1(X1) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl3_9 | spl3_1 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f61,f25,f67])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0] : (k2_mcart_1(X0) != k2_mcart_1(X1) | k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0) | X0 = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | ~m1_subset_1(X0,sK0)) ) | (spl3_1 | ~spl3_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f27])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1 | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f62,f23])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | k2_mcart_1(X0) != k2_mcart_1(X1) | X0 = X1) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_8 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f30,f61])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    spl3_2 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_mcart_1(X0) != k2_mcart_1(X1) | k1_mcart_1(X0) != k1_mcart_1(X1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0) | X0 = X1) ) | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f22,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f30])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | X0 = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (X0 = X2 | k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (X0 = X2 | (k2_mcart_1(X2) != k2_mcart_1(X0) | k1_mcart_1(X2) != k1_mcart_1(X0) | ~r2_hidden(X0,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : ((k2_mcart_1(X2) = k2_mcart_1(X0) & k1_mcart_1(X2) = k1_mcart_1(X0) & r2_hidden(X0,X1) & r2_hidden(X2,X1)) => X0 = X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f55])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k2_mcart_1(sK1) = k2_mcart_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ((sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0)) & m1_subset_1(sK1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) & v1_relat_1(sK0) & ~v1_xboole_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,sK0)) & m1_subset_1(X1,sK0)) => (? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) & m1_subset_1(sK1,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X2] : (sK1 != X2 & k2_mcart_1(X2) = k2_mcart_1(sK1) & k1_mcart_1(X2) = k1_mcart_1(sK1) & m1_subset_1(X2,sK0)) => (sK1 != sK2 & k2_mcart_1(sK1) = k2_mcart_1(sK2) & k1_mcart_1(sK1) = k1_mcart_1(sK2) & m1_subset_1(sK2,sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1))) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) & (v1_relat_1(X0) & ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1)) => X1 = X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ((k2_mcart_1(X2) = k2_mcart_1(X1) & k1_mcart_1(X2) = k1_mcart_1(X1)) => X1 = X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f50])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k1_mcart_1(sK1) = k1_mcart_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ~spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK1 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f40])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    m1_subset_1(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    m1_subset_1(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f25])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (31657)------------------------------
% 0.21/0.50  % (31657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31657)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (31657)Memory used [KB]: 6140
% 0.21/0.50  % (31657)Time elapsed: 0.094 s
% 0.21/0.50  % (31657)------------------------------
% 0.21/0.50  % (31657)------------------------------
% 0.21/0.50  % (31654)Success in time 0.136 s
%------------------------------------------------------------------------------
