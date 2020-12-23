%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 128 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  246 ( 412 expanded)
%              Number of equality atoms :   49 (  85 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f50,f54,f62,f66,f70,f74,f80,f86,f97,f103,f109])).

fof(f109,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f107,f30])).

fof(f30,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f107,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f106,f85])).

fof(f85,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_13
  <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f106,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f45,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f104,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_16 ),
    inference(resolution,[],[f102,f40])).

fof(f40,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_16
  <=> ! [X0] :
        ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f103,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f99,f95,f77,f33,f101])).

fof(f33,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( spl3_12
  <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f95,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f98,f79])).

fof(f79,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,k1_funct_1(k6_relat_1(sK1),sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(resolution,[],[f96,f35])).

fof(f35,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f96,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f93,f72,f60,f52,f48,f95])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f92,f53])).

fof(f53,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f91,f49])).

fof(f49,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f91,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f73,f61])).

fof(f61,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f86,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f64,f43,f84])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f80,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f68,f33,f77])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k1_funct_1(k6_relat_1(X1),X0) = X0
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( sK0 = k1_funct_1(k6_relat_1(sK1),sK0)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f35])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k6_relat_1(X1),X0) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f70,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f43])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f41,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f28])).

fof(f19,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:40:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (15490)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (15490)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f112,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f50,f54,f62,f66,f70,f74,f80,f86,f97,f103,f109])).
% 0.21/0.41  fof(f109,plain,(
% 0.21/0.41    spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_13 | ~spl3_16),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.41  fof(f108,plain,(
% 0.21/0.41    $false | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_13 | ~spl3_16)),
% 0.21/0.41    inference(subsumption_resolution,[],[f107,f30])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    spl3_1 <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f107,plain,(
% 0.21/0.41    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_13 | ~spl3_16)),
% 0.21/0.41    inference(forward_demodulation,[],[f106,f85])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | ~spl3_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f84])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    spl3_13 <=> ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.41  fof(f106,plain,(
% 0.21/0.41    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_16)),
% 0.21/0.41    inference(subsumption_resolution,[],[f104,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_16)),
% 0.21/0.41    inference(resolution,[],[f102,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    v1_funct_1(sK2) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f38])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    spl3_3 <=> v1_funct_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0) | ~v1_relat_1(X0)) ) | ~spl3_16),
% 0.21/0.41    inference(avatar_component_clause,[],[f101])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    spl3_16 <=> ! [X0] : (k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    spl3_16 | ~spl3_2 | ~spl3_12 | ~spl3_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f99,f95,f77,f33,f101])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl3_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f77,plain,(
% 0.21/0.41    spl3_12 <=> sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl3_15 <=> ! [X1,X0,X2] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    ( ! [X0] : (k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_12 | ~spl3_15)),
% 0.21/0.41    inference(forward_demodulation,[],[f98,f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) | ~spl3_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f77])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ( ! [X0] : (k1_funct_1(k5_relat_1(k6_relat_1(sK1),X0),sK0) = k1_funct_1(X0,k1_funct_1(k6_relat_1(sK1),sK0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_15)),
% 0.21/0.41    inference(resolution,[],[f96,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1) | ~spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f33])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl3_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f95])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    spl3_15 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f93,f72,f60,f52,f48,f95])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_5 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl3_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl3_8 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    spl3_11 <=> ! [X1,X0,X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_11)),
% 0.21/0.41    inference(subsumption_resolution,[],[f92,f53])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f52])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_5 | ~spl3_8 | ~spl3_11)),
% 0.21/0.41    inference(subsumption_resolution,[],[f91,f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k5_relat_1(k6_relat_1(X0),X2),X1) = k1_funct_1(X2,k1_funct_1(k6_relat_1(X0),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl3_8 | ~spl3_11)),
% 0.21/0.41    inference(superposition,[],[f73,f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f60])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f72])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    spl3_13 | ~spl3_4 | ~spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f81,f64,f43,f84])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl3_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f81,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.41    inference(resolution,[],[f65,f45])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f64])).
% 0.21/0.41  fof(f80,plain,(
% 0.21/0.41    spl3_12 | ~spl3_2 | ~spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f75,f68,f33,f77])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    spl3_10 <=> ! [X1,X0] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) | (~spl3_2 | ~spl3_10)),
% 0.21/0.41    inference(resolution,[],[f69,f35])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_funct_1(k6_relat_1(X1),X0) = X0) ) | ~spl3_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f68])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f26,f72])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f25,f68])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f64])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f60])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f52])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f48])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f16,f43])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    v1_relat_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) & r2_hidden(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.41    inference(flattening,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_funct_1(sK2)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ~spl3_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f28])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (15490)------------------------------
% 0.21/0.41  % (15490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (15490)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (15490)Memory used [KB]: 10618
% 0.21/0.41  % (15490)Time elapsed: 0.007 s
% 0.21/0.41  % (15490)------------------------------
% 0.21/0.41  % (15490)------------------------------
% 0.21/0.42  % (15484)Success in time 0.06 s
%------------------------------------------------------------------------------
