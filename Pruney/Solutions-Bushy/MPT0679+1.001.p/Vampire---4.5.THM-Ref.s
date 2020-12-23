%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0679+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 42.84s
% Output     : Refutation 42.84s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 347 expanded)
%              Number of leaves         :   34 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  663 (1802 expanded)
%              Number of equality atoms :  123 ( 372 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f13535,f37302,f37335,f37336,f37383,f37384,f37388,f37622,f37676,f37677,f37681,f38196,f38197,f48528,f48596])).

fof(f48596,plain,
    ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) != sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1)
    | ~ r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f48528,plain,
    ( spl10_1306
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_35
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f48527,f1134,f1124,f319,f309,f104,f99,f94,f48494])).

fof(f48494,plain,
    ( spl10_1306
  <=> sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1306])])).

fof(f94,plain,
    ( spl10_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f99,plain,
    ( spl10_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f104,plain,
    ( spl10_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f309,plain,
    ( spl10_8
  <=> sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f319,plain,
    ( spl10_10
  <=> r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1124,plain,
    ( spl10_35
  <=> sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f1134,plain,
    ( spl10_37
  <=> r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f48527,plain,
    ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_35
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f48437,f1126])).

fof(f1126,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f48437,plain,
    ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_37 ),
    inference(resolution,[],[f48428,f1136])).

fof(f1136,plain,
    ( r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f48428,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK2))
        | sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = X3
        | sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) != k1_funct_1(sK2,X3) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(forward_demodulation,[],[f1911,f311])).

fof(f311,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1911,plain,
    ( ! [X3] :
        ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = X3
        | k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) != k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1910,f106])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1910,plain,
    ( ! [X3] :
        ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = X3
        | k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) != k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1909,f101])).

fof(f101,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f1909,plain,
    ( ! [X3] :
        ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = X3
        | k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) != k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_2
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f1874,f96])).

fof(f96,plain,
    ( v2_funct_1(sK2)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1874,plain,
    ( ! [X3] :
        ( sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) = X3
        | k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))) != k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_10 ),
    inference(resolution,[],[f321,f45])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X3)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f321,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f319])).

fof(f38197,plain,
    ( ~ spl10_59
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f38162,f314,f2010])).

fof(f2010,plain,
    ( spl10_59
  <=> r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f314,plain,
    ( spl10_9
  <=> r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f38162,plain,
    ( ~ r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_9 ),
    inference(resolution,[],[f316,f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f67,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f316,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f314])).

fof(f38196,plain,
    ( spl10_60
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f38161,f314,f2015])).

fof(f2015,plain,
    ( spl10_60
  <=> r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f38161,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK0)
    | ~ spl10_9 ),
    inference(resolution,[],[f316,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f66,f58])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f37681,plain,
    ( spl10_35
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f37680,f383,f104,f99,f1124])).

fof(f383,plain,
    ( spl10_13
  <=> r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f37680,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f37679,f106])).

fof(f37679,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ v1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f37644,f101])).

fof(f37644,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_13 ),
    inference(resolution,[],[f385,f80])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f385,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f383])).

fof(f37677,plain,
    ( spl10_36
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f37633,f383,f104,f99,f1129])).

fof(f1129,plain,
    ( spl10_36
  <=> r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f37633,plain,
    ( r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK1)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f106,f101,f385,f81])).

fof(f81,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37676,plain,
    ( spl10_37
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f37634,f383,f104,f99,f1134])).

fof(f37634,plain,
    ( r2_hidden(sK7(sK2,sK1,sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f106,f101,f385,f82])).

fof(f82,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37622,plain,
    ( spl10_13
    | spl10_6
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f37586,f379,f200,f383])).

fof(f200,plain,
    ( spl10_6
  <=> r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f379,plain,
    ( spl10_12
  <=> r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f37586,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK1))
    | spl10_6
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f202,f380,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f380,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f379])).

fof(f202,plain,
    ( ~ r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f37388,plain,
    ( spl10_8
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f37387,f205,f104,f99,f309])).

fof(f205,plain,
    ( spl10_7
  <=> r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f37387,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f37386,f106])).

fof(f37386,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ v1_relat_1(sK2)
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f37348,f101])).

fof(f37348,plain,
    ( sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) = k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_7 ),
    inference(resolution,[],[f207,f80])).

fof(f207,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f205])).

fof(f37384,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f37338,f205,f104,f99,f314])).

fof(f37338,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k6_subset_1(sK0,sK1))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f106,f101,f207,f81])).

fof(f37383,plain,
    ( spl10_10
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f37339,f205,f104,f99,f319])).

fof(f37339,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),k1_relat_1(sK2))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f106,f101,f207,f82])).

fof(f37336,plain,
    ( spl10_7
    | spl10_5 ),
    inference(avatar_split_clause,[],[f37313,f172,f205])).

fof(f172,plain,
    ( spl10_5
  <=> r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f37313,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    | spl10_5 ),
    inference(unit_resulting_resolution,[],[f174,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f174,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl10_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f37335,plain,
    ( ~ spl10_6
    | spl10_5 ),
    inference(avatar_split_clause,[],[f37314,f172,f200])).

fof(f37314,plain,
    ( ~ r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl10_5 ),
    inference(unit_resulting_resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK8(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f37302,plain,
    ( ~ spl10_5
    | spl10_1
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f37286,f104,f89,f172])).

fof(f89,plain,
    ( spl10_1
  <=> k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f37286,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl10_1
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f91,f151])).

fof(f151,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k9_relat_1(sK2,k6_subset_1(X3,X4)),k6_subset_1(k9_relat_1(sK2,X3),k9_relat_1(sK2,X4)))
        | k9_relat_1(sK2,k6_subset_1(X3,X4)) = k6_subset_1(k9_relat_1(sK2,X3),k9_relat_1(sK2,X4)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_relat_1)).

fof(f91,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f13535,plain,
    ( spl10_12
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f13529,f2015,f319,f309,f104,f99,f379])).

fof(f13529,plain,
    ( r2_hidden(sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f13498,f311])).

fof(f13498,plain,
    ( r2_hidden(k1_funct_1(sK2,sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),k9_relat_1(sK2,sK0))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_60 ),
    inference(unit_resulting_resolution,[],[f106,f101,f321,f2017,f79])).

fof(f79,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2017,plain,
    ( r2_hidden(sK7(sK2,k6_subset_1(sK0,sK1),sK8(k9_relat_1(sK2,k6_subset_1(sK0,sK1)),k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),sK0)
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f2015])).

fof(f107,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
    & v2_funct_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
        & v2_funct_1(X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1))
      & v2_funct_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) != k9_relat_1(X2,k6_subset_1(X0,X1))
      & v2_funct_1(X2)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( v2_funct_1(X2)
         => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f102,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k9_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
