%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 134 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 491 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f55,f59,f63,f67,f94,f109,f174,f192,f204,f225])).

fof(f225,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f223,f45])).

fof(f45,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f223,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f222,f30])).

fof(f30,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f222,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_34 ),
    inference(resolution,[],[f203,f40])).

fof(f40,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f203,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_34
  <=> ! [X1] :
        ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f204,plain,
    ( spl4_34
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f200,f190,f53,f48,f202])).

fof(f48,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f53,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f190,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK1),X0)
        | r1_tarski(k9_relat_1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f200,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f194,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f194,plain,
    ( ! [X1] :
        ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_6
    | ~ spl4_32 ),
    inference(resolution,[],[f191,f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK1),X0)
        | r1_tarski(k9_relat_1(sK2,sK0),X0) )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl4_32
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f188,f171,f65,f190])).

fof(f65,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f171,plain,
    ( spl4_28
  <=> k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK1),X0)
        | r1_tarski(k9_relat_1(sK2,sK0),X0) )
    | ~ spl4_9
    | ~ spl4_28 ),
    inference(superposition,[],[f66,f173])).

fof(f173,plain,
    ( k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f174,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f166,f107,f33,f171])).

fof(f33,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f107,plain,
    ( spl4_17
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f166,plain,
    ( k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(resolution,[],[f108,f35])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f108,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f101,f92,f48,f107])).

fof(f92,plain,
    ( spl4_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f101,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)) )
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(resolution,[],[f93,f50])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,
    ( spl4_14
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f90,f61,f57,f92])).

fof(f57,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f61,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2)
        | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f67,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f63,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f59,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f55,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f51,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f38])).

fof(f20,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f33])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f28])).

fof(f22,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (2165)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.44  % (2162)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (2163)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (2164)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (2163)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f226,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f55,f59,f63,f67,f94,f109,f174,f192,f204,f225])).
% 0.21/0.45  fof(f225,plain,(
% 0.21/0.45    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_34),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f224])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f223,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f223,plain,(
% 0.21/0.45    ~v1_relat_1(sK3) | (spl4_1 | ~spl4_3 | ~spl4_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f222,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl4_1 <=> r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f222,plain,(
% 0.21/0.45    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_34)),
% 0.21/0.45    inference(resolution,[],[f203,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    ( ! [X1] : (~r1_tarski(sK2,X1) | r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1)) | ~v1_relat_1(X1)) ) | ~spl4_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f202])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    spl4_34 <=> ! [X1] : (r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    spl4_34 | ~spl4_5 | ~spl4_6 | ~spl4_32),
% 0.21/0.45    inference(avatar_split_clause,[],[f200,f190,f53,f48,f202])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl4_5 <=> v1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl4_6 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f190,plain,(
% 0.21/0.45    spl4_32 <=> ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK1),X0) | r1_tarski(k9_relat_1(sK2,sK0),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.45  fof(f200,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_6 | ~spl4_32)),
% 0.21/0.45    inference(subsumption_resolution,[],[f194,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    ( ! [X1] : (r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | (~spl4_6 | ~spl4_32)),
% 0.21/0.45    inference(resolution,[],[f191,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f191,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK1),X0) | r1_tarski(k9_relat_1(sK2,sK0),X0)) ) | ~spl4_32),
% 0.21/0.45    inference(avatar_component_clause,[],[f190])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    spl4_32 | ~spl4_9 | ~spl4_28),
% 0.21/0.45    inference(avatar_split_clause,[],[f188,f171,f65,f190])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl4_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    spl4_28 <=> k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.45  fof(f188,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK1),X0) | r1_tarski(k9_relat_1(sK2,sK0),X0)) ) | (~spl4_9 | ~spl4_28)),
% 0.21/0.45    inference(superposition,[],[f66,f173])).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | ~spl4_28),
% 0.21/0.45    inference(avatar_component_clause,[],[f171])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f174,plain,(
% 0.21/0.45    spl4_28 | ~spl4_2 | ~spl4_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f166,f107,f33,f171])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl4_17 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    k9_relat_1(sK2,sK1) = k2_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_2 | ~spl4_17)),
% 0.21/0.45    inference(resolution,[],[f108,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3))) ) | ~spl4_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f107])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    spl4_17 | ~spl4_5 | ~spl4_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f92,f48,f107])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl4_14 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_relat_1(sK2,X3) = k2_xboole_0(k9_relat_1(sK2,X2),k9_relat_1(sK2,X3))) ) | (~spl4_5 | ~spl4_14)),
% 0.21/0.45    inference(resolution,[],[f93,f50])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) | ~spl4_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f92])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl4_14 | ~spl4_7 | ~spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f90,f61,f57,f92])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl4_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k9_relat_1(X2,X1) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) | (~spl4_7 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f62,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl4_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f57])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) ) | ~spl4_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl4_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl4_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl4_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl4_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f48])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f16,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X3] : (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.45    inference(flattening,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f5])).
% 0.21/0.45  fof(f5,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f43])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    v1_relat_1(sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f38])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    r1_tarski(sK2,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f33])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ~spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f28])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK3,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (2163)------------------------------
% 0.21/0.45  % (2163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (2163)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (2163)Memory used [KB]: 10618
% 0.21/0.45  % (2163)Time elapsed: 0.013 s
% 0.21/0.45  % (2163)------------------------------
% 0.21/0.45  % (2163)------------------------------
% 0.21/0.45  % (2157)Success in time 0.1 s
%------------------------------------------------------------------------------
