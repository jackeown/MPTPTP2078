%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0663+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  83 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  142 ( 267 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f37,f41,f45,f50,f57,f60])).

fof(f60,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f58,f21])).

fof(f21,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_2
  <=> r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),X0))
        | k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),X0))
        | k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f57,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f53,f48,f43,f34,f29,f55])).

fof(f29,plain,
    ( spl3_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f34,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( spl3_7
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),X0))
        | k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f52,f36])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),X0))
        | k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f51,f31])).

fof(f31,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),X0))
        | k1_funct_1(k7_relat_1(sK2,X0),X1) = k1_funct_1(sK2,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f44,f49])).

fof(f49,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f50,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f46,f39,f34,f48])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k3_xboole_0(k1_relat_1(sK2),X0)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f34])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f19])).

fof(f15,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
