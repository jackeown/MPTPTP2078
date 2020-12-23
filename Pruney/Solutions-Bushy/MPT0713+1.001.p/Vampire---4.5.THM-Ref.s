%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0713+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 147 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 395 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f91,f147,f155,f166,f202,f211,f236,f361,f422,f436,f851,f852])).

fof(f852,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0)
    | r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f851,plain,
    ( spl7_6
    | ~ spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f849,f133,f151,f106])).

fof(f106,plain,
    ( spl7_6
  <=> r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f151,plain,
    ( spl7_12
  <=> r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f133,plain,
    ( spl7_10
  <=> k1_funct_1(sK1,sK0) = sK5(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f849,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_10 ),
    inference(superposition,[],[f44,f135])).

fof(f135,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f436,plain,
    ( spl7_47
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f410,f358,f192,f184,f433])).

fof(f433,plain,
    ( spl7_47
  <=> r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f184,plain,
    ( spl7_14
  <=> v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f192,plain,
    ( spl7_16
  <=> v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f358,plain,
    ( spl7_37
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f410,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | r2_hidden(k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_37 ),
    inference(resolution,[],[f360,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f360,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f358])).

fof(f422,plain,
    ( spl7_44
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f405,f358,f73,f78,f419])).

fof(f419,plain,
    ( spl7_44
  <=> k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f78,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f73,plain,
    ( spl7_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f405,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK0) = k1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)),sK0)
    | ~ spl7_37 ),
    inference(resolution,[],[f360,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

fof(f361,plain,
    ( spl7_37
    | ~ spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f352,f68,f78,f358])).

fof(f68,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f352,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_2 ),
    inference(resolution,[],[f203,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(k7_relat_1(X0,k1_tarski(X1)))) ) ),
    inference(resolution,[],[f51,f61])).

fof(f61,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f236,plain,
    ( spl7_10
    | spl7_6 ),
    inference(avatar_split_clause,[],[f235,f106,f133])).

fof(f235,plain,
    ( k1_funct_1(sK1,sK0) = sK5(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | spl7_6 ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f211,plain,
    ( ~ spl7_5
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl7_5
    | spl7_16 ),
    inference(resolution,[],[f194,f90])).

fof(f90,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK1,X0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_5
  <=> ! [X0] : v1_funct_1(k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f194,plain,
    ( ~ v1_funct_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f202,plain,
    ( ~ spl7_4
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl7_4
    | spl7_14 ),
    inference(resolution,[],[f186,f83])).

fof(f83,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl7_4 ),
    inference(resolution,[],[f35,f80])).

fof(f80,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f186,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k1_tarski(sK0)))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f166,plain,
    ( spl7_7
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl7_7
    | ~ spl7_11 ),
    inference(resolution,[],[f146,f112])).

fof(f112,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_7
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f146,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(X0))),k1_tarski(k1_funct_1(sK1,X0)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_11
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(X0))),k1_tarski(k1_funct_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f155,plain,
    ( spl7_1
    | ~ spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f149,f106,f110,f63])).

fof(f63,plain,
    ( spl7_1
  <=> k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = k1_tarski(k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f149,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) = k1_tarski(k1_funct_1(sK1,sK0))
    | ~ spl7_6 ),
    inference(resolution,[],[f107,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f107,plain,
    ( r1_tarski(k1_tarski(k1_funct_1(sK1,sK0)),k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f147,plain,
    ( spl7_11
    | ~ spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f142,f73,f78,f145])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(X0))),k1_tarski(k1_funct_1(sK1,X0))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f36,f75])).

fof(f75,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

fof(f91,plain,
    ( spl7_5
    | ~ spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f87,f73,f78,f89])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | v1_funct_1(k7_relat_1(sK1,X0)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f38,f75])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f81,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f25,f78])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

fof(f76,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f26,f73])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
