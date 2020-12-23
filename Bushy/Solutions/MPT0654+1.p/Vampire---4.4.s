%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t61_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 444 expanded)
%              Number of leaves         :   46 ( 181 expanded)
%              Depth                    :   15
%              Number of atoms          :  787 (1426 expanded)
%              Number of equality atoms :  152 ( 331 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f88,f95,f102,f115,f128,f141,f162,f169,f208,f219,f244,f254,f273,f278,f283,f291,f298,f305,f312,f316,f321,f361,f391,f442,f452,f459,f481,f489])).

fof(f489,plain,
    ( ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_38
    | spl2_47 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_38
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f487,f311])).

fof(f311,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) != sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl2_47
  <=> k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) != sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f487,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) = sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f486,f80])).

fof(f80,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f486,plain,
    ( ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) = sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f485,f94])).

fof(f94,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f485,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) = sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_2
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f482,f87])).

fof(f87,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f482,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) = sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_38 ),
    inference(resolution,[],[f272,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t57_funct_1)).

fof(f272,plain,
    ( r2_hidden(sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl2_38
  <=> r2_hidden(sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f481,plain,
    ( ~ spl2_57
    | ~ spl2_10
    | spl2_31 ),
    inference(avatar_split_clause,[],[f414,f239,f110,f479])).

fof(f479,plain,
    ( spl2_57
  <=> ~ r2_hidden(sK1(k1_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f110,plain,
    ( spl2_10
  <=> k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f239,plain,
    ( spl2_31
  <=> ~ r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f414,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(sK0),k6_relat_1(k1_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl2_10
    | ~ spl2_31 ),
    inference(backward_demodulation,[],[f111,f240])).

fof(f240,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f239])).

fof(f111,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f459,plain,
    ( spl2_54
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f406,f139,f110,f457])).

fof(f457,plain,
    ( spl2_54
  <=> k1_relat_1(sK0) = k2_relat_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f139,plain,
    ( spl2_14
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f406,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f111,f140])).

fof(f140,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f452,plain,
    ( spl2_52
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f405,f126,f110,f450])).

fof(f450,plain,
    ( spl2_52
  <=> k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f126,plain,
    ( spl2_12
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f405,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f111,f127])).

fof(f127,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f442,plain,
    ( spl2_50
    | ~ spl2_10
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f413,f233,f110,f440])).

fof(f440,plain,
    ( spl2_50
  <=> v1_funct_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f233,plain,
    ( spl2_28
  <=> v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f413,plain,
    ( v1_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl2_10
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f111,f234])).

fof(f234,plain,
    ( v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f391,plain,
    ( ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_30
    | spl2_45 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_30
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f389,f304])).

fof(f304,plain,
    ( k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) != sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl2_45
  <=> k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) != sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f389,plain,
    ( k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f388,f80])).

fof(f388,plain,
    ( ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f387,f94])).

fof(f387,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f384,f87])).

fof(f384,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_30 ),
    inference(resolution,[],[f243,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t56_funct_1)).

fof(f243,plain,
    ( r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl2_30
  <=> r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f361,plain,
    ( spl2_48
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f326,f160,f104,f359])).

fof(f359,plain,
    ( spl2_48
  <=> k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f104,plain,
    ( spl2_8
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f160,plain,
    ( spl2_16
  <=> k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f326,plain,
    ( k1_relat_1(k6_relat_1(k2_relat_1(sK0))) = k2_relat_1(sK0)
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(backward_demodulation,[],[f105,f161])).

fof(f161,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f105,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f321,plain,
    ( ~ spl2_0
    | ~ spl2_2
    | ~ spl2_32
    | spl2_37
    | ~ spl2_42 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_37
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f294,f319])).

fof(f319,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_32
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f318,f250])).

fof(f250,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_32
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f318,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f317,f87])).

fof(f317,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f284,f80])).

fof(f284,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_37 ),
    inference(resolution,[],[f266,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',fc2_funct_1)).

fof(f266,plain,
    ( ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl2_37
  <=> ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f294,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl2_42
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f316,plain,
    ( ~ spl2_0
    | ~ spl2_2
    | spl2_43 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f314,f80])).

fof(f314,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_43 ),
    inference(subsumption_resolution,[],[f313,f87])).

fof(f313,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_43 ),
    inference(resolution,[],[f297,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',dt_k2_funct_1)).

fof(f297,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl2_43
  <=> ~ v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f312,plain,
    ( ~ spl2_35
    | ~ spl2_37
    | ~ spl2_47
    | spl2_9
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f177,f160,f107,f310,f265,f259])).

fof(f259,plain,
    ( spl2_35
  <=> ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f107,plain,
    ( spl2_9
  <=> k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f177,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) != sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f176,f108])).

fof(f108,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f176,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) != sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f172,f161])).

fof(f172,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))) != sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f73,f161])).

fof(f73,plain,(
    ! [X1] :
      ( k1_funct_1(X1,sK1(k1_relat_1(X1),X1)) != sK1(k1_relat_1(X1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | k1_funct_1(X1,sK1(X0,X1)) != sK1(X0,X1)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t34_funct_1)).

fof(f305,plain,
    ( ~ spl2_27
    | ~ spl2_29
    | ~ spl2_45
    | spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f155,f126,f113,f303,f236,f230])).

fof(f230,plain,
    ( spl2_27
  <=> ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f236,plain,
    ( spl2_29
  <=> ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f113,plain,
    ( spl2_11
  <=> k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f155,plain,
    ( k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) != sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f154,f114])).

fof(f114,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f154,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) != sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f153,f127])).

fof(f153,plain,
    ( k1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) != sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))))
    | ~ spl2_12 ),
    inference(superposition,[],[f73,f127])).

fof(f298,plain,
    ( ~ spl2_43
    | ~ spl2_33
    | ~ spl2_0
    | ~ spl2_2
    | spl2_29 ),
    inference(avatar_split_clause,[],[f280,f236,f86,f79,f252,f296])).

fof(f252,plain,
    ( spl2_33
  <=> ~ v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f280,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f279,f80])).

fof(f279,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f247,f87])).

fof(f247,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_29 ),
    inference(resolution,[],[f237,f68])).

fof(f237,plain,
    ( ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f236])).

fof(f291,plain,
    ( ~ spl2_29
    | ~ spl2_27
    | spl2_40
    | ~ spl2_2
    | spl2_11
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f212,f200,f126,f113,f86,f289,f230,f236])).

fof(f289,plain,
    ( spl2_40
  <=> k1_funct_1(sK0,sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f200,plain,
    ( spl2_20
  <=> k6_relat_1(k1_relat_1(sK0)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f212,plain,
    ( k1_funct_1(sK0,sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f211,f201])).

fof(f201,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = sK0
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f211,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f209,f87])).

fof(f209,plain,
    ( ~ v1_funct_1(sK0)
    | k1_funct_1(k6_relat_1(k1_relat_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(backward_demodulation,[],[f201,f192])).

fof(f192,plain,
    ( k1_funct_1(k6_relat_1(k1_relat_1(sK0)),sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f191,f127])).

fof(f191,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f190,f114])).

fof(f190,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f188,f127])).

fof(f188,plain,
    ( ~ v1_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_funct_1(k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))) = sK1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))),k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_12 ),
    inference(superposition,[],[f143,f127])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK1(k1_relat_1(X0),X0)) = sK1(k1_relat_1(X0),X0) ) ),
    inference(subsumption_resolution,[],[f142,f65])).

fof(f65,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',dt_k6_relat_1)).

fof(f142,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(X0)))
      | k1_funct_1(k6_relat_1(k1_relat_1(X0)),sK1(k1_relat_1(X0),X0)) = sK1(k1_relat_1(X0),X0) ) ),
    inference(resolution,[],[f74,f72])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X1] :
      ( r2_hidden(sK1(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK1(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f283,plain,
    ( ~ spl2_0
    | ~ spl2_32
    | spl2_35 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_32
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f250,f281])).

fof(f281,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_35 ),
    inference(subsumption_resolution,[],[f274,f80])).

fof(f274,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_35 ),
    inference(resolution,[],[f260,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',dt_k5_relat_1)).

fof(f260,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f259])).

fof(f278,plain,
    ( ~ spl2_0
    | ~ spl2_2
    | spl2_33 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f276,f80])).

fof(f276,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f275,f87])).

fof(f275,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_33 ),
    inference(resolution,[],[f253,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f253,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f252])).

fof(f273,plain,
    ( ~ spl2_35
    | ~ spl2_37
    | spl2_38
    | spl2_9
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f179,f160,f107,f271,f265,f259])).

fof(f179,plain,
    ( r2_hidden(sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f178,f108])).

fof(f178,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | r2_hidden(sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f175,f161])).

fof(f175,plain,
    ( r2_hidden(sK1(k2_relat_1(sK0),k5_relat_1(k2_funct_1(sK0),sK0)),k2_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f74,f161])).

fof(f254,plain,
    ( ~ spl2_33
    | ~ spl2_0
    | spl2_27 ),
    inference(avatar_split_clause,[],[f246,f230,f79,f252])).

fof(f246,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_0
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f245,f80])).

fof(f245,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_27 ),
    inference(resolution,[],[f231,f66])).

fof(f231,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f244,plain,
    ( ~ spl2_27
    | ~ spl2_29
    | spl2_30
    | spl2_11
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f146,f126,f113,f242,f236,f230])).

fof(f146,plain,
    ( r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f145,f114])).

fof(f145,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))
    | r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f144,f127])).

fof(f144,plain,
    ( r2_hidden(sK1(k1_relat_1(sK0),k5_relat_1(sK0,k2_funct_1(sK0))),k1_relat_1(sK0))
    | ~ v1_funct_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))))
    | ~ spl2_12 ),
    inference(superposition,[],[f74,f127])).

fof(f219,plain,
    ( ~ spl2_25
    | spl2_11
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f210,f200,f113,f217])).

fof(f217,plain,
    ( spl2_25
  <=> k5_relat_1(sK0,k2_funct_1(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f210,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != sK0
    | ~ spl2_11
    | ~ spl2_20 ),
    inference(backward_demodulation,[],[f201,f114])).

fof(f208,plain,
    ( spl2_20
    | spl2_22
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f184,f93,f86,f79,f206,f200])).

fof(f206,plain,
    ( spl2_22
  <=> k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK1(k1_relat_1(sK0),sK0))) = sK1(k1_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f184,plain,
    ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK1(k1_relat_1(sK0),sK0))) = sK1(k1_relat_1(sK0),sK0)
    | k6_relat_1(k1_relat_1(sK0)) = sK0
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f183,f80])).

fof(f183,plain,
    ( ~ v1_relat_1(sK0)
    | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK1(k1_relat_1(sK0),sK0))) = sK1(k1_relat_1(sK0),sK0)
    | k6_relat_1(k1_relat_1(sK0)) = sK0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f182,f87])).

fof(f182,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK1(k1_relat_1(sK0),sK0))) = sK1(k1_relat_1(sK0),sK0)
    | k6_relat_1(k1_relat_1(sK0)) = sK0
    | ~ spl2_4 ),
    inference(resolution,[],[f149,f94])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK1(k1_relat_1(X0),X0))) = sK1(k1_relat_1(X0),X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,sK1(k1_relat_1(X0),X0))) = sK1(k1_relat_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f61,f74])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f169,plain,
    ( spl2_18
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f134,f93,f86,f79,f167])).

fof(f167,plain,
    ( spl2_18
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f134,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f133,f80])).

fof(f133,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f132,f87])).

fof(f132,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f55,f94])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t59_funct_1)).

fof(f162,plain,
    ( spl2_16
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f131,f93,f86,f79,f160])).

fof(f131,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f130,f80])).

fof(f130,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f129,f87])).

fof(f129,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f54,f94])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( spl2_14
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f93,f86,f79,f139])).

fof(f121,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f120,f80])).

fof(f120,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f119,f87])).

fof(f119,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f94])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t58_funct_1)).

fof(f128,plain,
    ( spl2_12
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f118,f93,f86,f79,f126])).

fof(f118,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f117,f80])).

fof(f117,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f116,f87])).

fof(f116,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f52,f94])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f115,plain,
    ( ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f46,f113,f107])).

fof(f46,plain,
    ( k5_relat_1(sK0,k2_funct_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) != k6_relat_1(k2_relat_1(X0))
        | k5_relat_1(X0,k2_funct_1(X0)) != k6_relat_1(k1_relat_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
            & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',t61_funct_1)).

fof(f102,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f64,f100])).

fof(f100,plain,
    ( spl2_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t61_funct_1.p',d2_xboole_0)).

fof(f95,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f48,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f47,f79])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
