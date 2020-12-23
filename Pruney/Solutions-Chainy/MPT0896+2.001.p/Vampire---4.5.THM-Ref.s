%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:12 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 443 expanded)
%              Number of leaves         :   36 ( 168 expanded)
%              Depth                    :   13
%              Number of atoms          :  557 (1799 expanded)
%              Number of equality atoms :  365 (1525 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f243,f777,f893,f924,f1099,f1285,f1535,f1650,f1734,f1764,f1924,f2170,f2308,f2416,f2417,f2426,f2452,f2479,f4589,f4593,f4674,f4766,f5235,f5237])).

fof(f5237,plain,
    ( spl11_3
    | ~ spl11_13 ),
    inference(avatar_contradiction_clause,[],[f5236])).

fof(f5236,plain,
    ( $false
    | spl11_3
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f3615,f239])).

fof(f239,plain,
    ( sK2 != sK6
    | spl11_3 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl11_3
  <=> sK2 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f3615,plain,
    ( sK2 = sK6
    | ~ spl11_13 ),
    inference(equality_resolution,[],[f338])).

fof(f338,plain,
    ( ! [X26,X27,X25] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27)
        | sK6 = X26 )
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl11_13
  <=> ! [X25,X27,X26] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27)
        | sK6 = X26 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f5235,plain,
    ( spl11_31
    | spl11_32
    | spl11_2
    | ~ spl11_171 ),
    inference(avatar_split_clause,[],[f5232,f4591,f235,f488,f485])).

fof(f485,plain,
    ( spl11_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f488,plain,
    ( spl11_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f235,plain,
    ( spl11_2
  <=> sK1 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f4591,plain,
    ( spl11_171
  <=> sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_171])])).

fof(f5232,plain,
    ( sK1 = sK5
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_171 ),
    inference(superposition,[],[f152,f4592])).

fof(f4592,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl11_171 ),
    inference(avatar_component_clause,[],[f4591])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f4766,plain,
    ( ~ spl11_186
    | spl11_1
    | ~ spl11_170 ),
    inference(avatar_split_clause,[],[f4761,f4587,f232,f4672])).

fof(f4672,plain,
    ( spl11_186
  <=> r1_tarski(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_186])])).

fof(f232,plain,
    ( spl11_1
  <=> sK0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f4587,plain,
    ( spl11_170
  <=> sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_170])])).

fof(f4761,plain,
    ( sK0 = sK4
    | ~ r1_tarski(sK0,sK4)
    | ~ spl11_170 ),
    inference(resolution,[],[f4752,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4752,plain,
    ( r1_tarski(sK4,sK0)
    | ~ spl11_170 ),
    inference(superposition,[],[f116,f4588])).

fof(f4588,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl11_170 ),
    inference(avatar_component_clause,[],[f4587])).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f4674,plain,
    ( spl11_31
    | spl11_32
    | spl11_186
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f4666,f341,f4672,f488,f485])).

fof(f341,plain,
    ( spl11_14
  <=> ! [X32,X31,X33] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33)
        | k2_zfmisc_1(sK4,sK5) = X31 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f4666,plain,
    ( r1_tarski(sK0,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_14 ),
    inference(superposition,[],[f4534,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4534,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK4)
    | ~ spl11_14 ),
    inference(superposition,[],[f116,f4486])).

fof(f4486,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)
    | ~ spl11_14 ),
    inference(equality_resolution,[],[f342])).

fof(f342,plain,
    ( ! [X33,X31,X32] :
        ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33)
        | k2_zfmisc_1(sK4,sK5) = X31 )
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f341])).

fof(f4593,plain,
    ( spl11_5
    | spl11_6
    | spl11_171
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f4539,f341,f4591,f312,f309])).

fof(f309,plain,
    ( spl11_5
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f312,plain,
    ( spl11_6
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f4539,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl11_14 ),
    inference(superposition,[],[f152,f4486])).

fof(f4589,plain,
    ( spl11_5
    | spl11_6
    | spl11_170
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f4538,f341,f4587,f312,f309])).

fof(f4538,plain,
    ( sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl11_14 ),
    inference(superposition,[],[f151,f4486])).

fof(f2479,plain,
    ( ~ spl11_95
    | spl11_4
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f2475,f378,f241,f2450])).

fof(f2450,plain,
    ( spl11_95
  <=> r1_tarski(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).

fof(f241,plain,
    ( spl11_4
  <=> sK3 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f378,plain,
    ( spl11_22
  <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f2475,plain,
    ( sK3 = sK7
    | ~ r1_tarski(sK3,sK7)
    | ~ spl11_22 ),
    inference(resolution,[],[f2456,f134])).

fof(f2456,plain,
    ( r1_tarski(sK7,sK3)
    | ~ spl11_22 ),
    inference(superposition,[],[f115,f379])).

fof(f379,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f378])).

fof(f115,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f2452,plain,
    ( spl11_45
    | spl11_95 ),
    inference(avatar_split_clause,[],[f2448,f2450,f541])).

fof(f541,plain,
    ( spl11_45
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f2448,plain,
    ( r1_tarski(sK3,sK7)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(global_subsumption,[],[f101,f2443])).

fof(f2443,plain,
    ( r1_tarski(sK3,sK7)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(superposition,[],[f270,f152])).

fof(f270,plain,(
    r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),sK7) ),
    inference(superposition,[],[f115,f185])).

fof(f185,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f97,f168,f168])).

fof(f168,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f97,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f49,f70])).

fof(f70,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f45])).

fof(f45,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f101,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f71])).

fof(f2426,plain,
    ( spl11_20
    | spl11_8
    | spl11_22 ),
    inference(avatar_split_clause,[],[f2380,f378,f318,f370])).

fof(f370,plain,
    ( spl11_20
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f318,plain,
    ( spl11_8
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f2380,plain,
    ( sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) ),
    inference(superposition,[],[f152,f185])).

fof(f2417,plain,
    ( spl11_10
    | spl11_7
    | spl11_8
    | spl11_14 ),
    inference(avatar_split_clause,[],[f2361,f341,f318,f315,f325])).

fof(f325,plain,
    ( spl11_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f315,plain,
    ( spl11_7
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f2361,plain,(
    ! [X33,X31,X32] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33)
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
      | k2_zfmisc_1(sK4,sK5) = X31 ) ),
    inference(superposition,[],[f215,f185])).

fof(f215,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f177,f154,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f177,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f2416,plain,
    ( spl11_10
    | spl11_7
    | spl11_8
    | spl11_13 ),
    inference(avatar_split_clause,[],[f2359,f337,f318,f315,f325])).

fof(f2359,plain,(
    ! [X26,X27,X25] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27)
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
      | sK6 = X26 ) ),
    inference(superposition,[],[f214,f185])).

fof(f214,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f178,f154,f154])).

fof(f178,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X1 = X4
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2308,plain,
    ( spl11_35
    | spl11_33
    | ~ spl11_45 ),
    inference(avatar_split_clause,[],[f2307,f541,f491,f498])).

fof(f498,plain,
    ( spl11_35
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f491,plain,
    ( spl11_33
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f2307,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_45 ),
    inference(duplicate_literal_removal,[],[f2306])).

fof(f2306,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_45 ),
    inference(forward_demodulation,[],[f2247,f104])).

fof(f104,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f2247,plain,
    ( k2_relat_1(k1_xboole_0) = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_45 ),
    inference(superposition,[],[f152,f542])).

fof(f542,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f541])).

fof(f2170,plain,
    ( spl11_10
    | spl11_7
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f2169,f370,f315,f325])).

fof(f2169,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl11_20 ),
    inference(duplicate_literal_removal,[],[f2168])).

fof(f2168,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl11_20 ),
    inference(forward_demodulation,[],[f2108,f104])).

fof(f2108,plain,
    ( k2_relat_1(k1_xboole_0) = sK6
    | k1_xboole_0 = sK6
    | k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl11_20 ),
    inference(superposition,[],[f152,f371])).

fof(f371,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1924,plain,
    ( spl11_31
    | spl11_32
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f1923,f498,f488,f485])).

fof(f1923,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_35 ),
    inference(duplicate_literal_removal,[],[f1922])).

fof(f1922,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_35 ),
    inference(forward_demodulation,[],[f1865,f104])).

fof(f1865,plain,
    ( k2_relat_1(k1_xboole_0) = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl11_35 ),
    inference(superposition,[],[f152,f499])).

fof(f499,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f498])).

fof(f1764,plain,(
    ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f1762])).

fof(f1762,plain,
    ( $false
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f99,f489])).

fof(f489,plain,
    ( k1_xboole_0 = sK1
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f488])).

fof(f99,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f71])).

fof(f1734,plain,
    ( spl11_45
    | spl11_34
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f1733,f318,f494,f541])).

fof(f494,plain,
    ( spl11_34
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f1733,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f1732])).

fof(f1732,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_8 ),
    inference(forward_demodulation,[],[f1683,f104])).

fof(f1683,plain,
    ( k2_relat_1(k1_xboole_0) = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_8 ),
    inference(superposition,[],[f152,f1421])).

fof(f1421,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl11_8 ),
    inference(forward_demodulation,[],[f1419,f222])).

fof(f222,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1419,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0)
    | ~ spl11_8 ),
    inference(backward_demodulation,[],[f185,f319])).

fof(f319,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f318])).

fof(f1650,plain,(
    ~ spl11_31 ),
    inference(avatar_contradiction_clause,[],[f1647])).

fof(f1647,plain,
    ( $false
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f98,f486])).

fof(f486,plain,
    ( k1_xboole_0 = sK0
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f485])).

fof(f98,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f71])).

fof(f1535,plain,(
    ~ spl11_33 ),
    inference(avatar_contradiction_clause,[],[f1533])).

fof(f1533,plain,
    ( $false
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f100,f492])).

fof(f492,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f491])).

fof(f100,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

fof(f1285,plain,
    ( spl11_5
    | spl11_6
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f1284,f325,f312,f309])).

fof(f1284,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl11_10 ),
    inference(duplicate_literal_removal,[],[f1283])).

fof(f1283,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f1226,f104])).

fof(f1226,plain,
    ( k2_relat_1(k1_xboole_0) = sK5
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | ~ spl11_10 ),
    inference(superposition,[],[f152,f326])).

fof(f326,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK4,sK5)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1099,plain,
    ( spl11_45
    | spl11_34
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f1098,f312,f494,f541])).

fof(f1098,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f1097])).

fof(f1097,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_6 ),
    inference(forward_demodulation,[],[f1047,f104])).

fof(f1047,plain,
    ( k2_relat_1(k1_xboole_0) = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_6 ),
    inference(superposition,[],[f152,f1014])).

fof(f1014,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl11_6 ),
    inference(forward_demodulation,[],[f1013,f229])).

fof(f229,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) ),
    inference(equality_resolution,[],[f207])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f171,f168])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f1013,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7)
    | ~ spl11_6 ),
    inference(backward_demodulation,[],[f185,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK5
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f312])).

fof(f924,plain,(
    ~ spl11_34 ),
    inference(avatar_contradiction_clause,[],[f921])).

fof(f921,plain,
    ( $false
    | ~ spl11_34 ),
    inference(subsumption_resolution,[],[f101,f495])).

fof(f495,plain,
    ( k1_xboole_0 = sK3
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f494])).

fof(f893,plain,
    ( spl11_45
    | spl11_34
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f892,f309,f494,f541])).

fof(f892,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_5 ),
    inference(duplicate_literal_removal,[],[f891])).

fof(f891,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f840,f104])).

fof(f840,plain,
    ( k2_relat_1(k1_xboole_0) = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_5 ),
    inference(superposition,[],[f152,f807])).

fof(f807,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f806,f230])).

fof(f230,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f170,f168])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f806,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7)
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f185,f310])).

fof(f310,plain,
    ( k1_xboole_0 = sK4
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f309])).

fof(f777,plain,
    ( spl11_45
    | spl11_34
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f776,f315,f494,f541])).

fof(f776,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_7 ),
    inference(duplicate_literal_removal,[],[f775])).

fof(f775,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f724,f104])).

fof(f724,plain,
    ( k2_relat_1(k1_xboole_0) = sK3
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl11_7 ),
    inference(superposition,[],[f152,f691])).

fof(f691,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f690,f225])).

fof(f225,plain,(
    ! [X2,X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2) ),
    inference(equality_resolution,[],[f202])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f164,f154])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f690,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7)
    | ~ spl11_7 ),
    inference(backward_demodulation,[],[f185,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK6
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f315])).

fof(f243,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f102,f241,f238,f235,f232])).

fof(f102,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (30750)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (30758)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (30729)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (30731)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30744)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (30730)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (30736)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (30746)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (30735)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (30738)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (30743)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (30733)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (30753)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (30751)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (30732)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (30754)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (30745)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (30746)Refutation not found, incomplete strategy% (30746)------------------------------
% 0.21/0.55  % (30746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30746)Memory used [KB]: 10618
% 0.21/0.55  % (30746)Time elapsed: 0.144 s
% 0.21/0.55  % (30746)------------------------------
% 0.21/0.55  % (30746)------------------------------
% 0.21/0.55  % (30742)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (30737)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (30741)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (30757)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (30739)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (30749)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (30756)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (30752)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (30740)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (30752)Refutation not found, incomplete strategy% (30752)------------------------------
% 0.21/0.57  % (30752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (30752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (30752)Memory used [KB]: 1791
% 0.21/0.57  % (30752)Time elapsed: 0.169 s
% 0.21/0.57  % (30752)------------------------------
% 0.21/0.57  % (30752)------------------------------
% 0.21/0.57  % (30748)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (30755)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (30747)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (30749)Refutation not found, incomplete strategy% (30749)------------------------------
% 0.21/0.59  % (30749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (30749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (30749)Memory used [KB]: 10874
% 0.21/0.59  % (30749)Time elapsed: 0.181 s
% 0.21/0.59  % (30749)------------------------------
% 0.21/0.59  % (30749)------------------------------
% 0.21/0.60  % (30734)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.08/0.67  % (30759)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.65/0.75  % (30761)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.65/0.75  % (30760)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.13/0.80  % (30731)Refutation found. Thanks to Tanya!
% 3.13/0.80  % SZS status Theorem for theBenchmark
% 3.13/0.80  % SZS output start Proof for theBenchmark
% 3.13/0.80  fof(f5238,plain,(
% 3.13/0.80    $false),
% 3.13/0.80    inference(avatar_sat_refutation,[],[f243,f777,f893,f924,f1099,f1285,f1535,f1650,f1734,f1764,f1924,f2170,f2308,f2416,f2417,f2426,f2452,f2479,f4589,f4593,f4674,f4766,f5235,f5237])).
% 3.13/0.80  fof(f5237,plain,(
% 3.13/0.80    spl11_3 | ~spl11_13),
% 3.13/0.80    inference(avatar_contradiction_clause,[],[f5236])).
% 3.13/0.80  fof(f5236,plain,(
% 3.13/0.80    $false | (spl11_3 | ~spl11_13)),
% 3.13/0.80    inference(subsumption_resolution,[],[f3615,f239])).
% 3.13/0.80  fof(f239,plain,(
% 3.13/0.80    sK2 != sK6 | spl11_3),
% 3.13/0.80    inference(avatar_component_clause,[],[f238])).
% 3.13/0.80  fof(f238,plain,(
% 3.13/0.80    spl11_3 <=> sK2 = sK6),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 3.13/0.80  fof(f3615,plain,(
% 3.13/0.80    sK2 = sK6 | ~spl11_13),
% 3.13/0.80    inference(equality_resolution,[],[f338])).
% 3.13/0.80  fof(f338,plain,(
% 3.13/0.80    ( ! [X26,X27,X25] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27) | sK6 = X26) ) | ~spl11_13),
% 3.13/0.80    inference(avatar_component_clause,[],[f337])).
% 3.13/0.80  fof(f337,plain,(
% 3.13/0.80    spl11_13 <=> ! [X25,X27,X26] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27) | sK6 = X26)),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 3.13/0.80  fof(f5235,plain,(
% 3.13/0.80    spl11_31 | spl11_32 | spl11_2 | ~spl11_171),
% 3.13/0.80    inference(avatar_split_clause,[],[f5232,f4591,f235,f488,f485])).
% 3.13/0.80  fof(f485,plain,(
% 3.13/0.80    spl11_31 <=> k1_xboole_0 = sK0),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 3.13/0.80  fof(f488,plain,(
% 3.13/0.80    spl11_32 <=> k1_xboole_0 = sK1),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 3.13/0.80  fof(f235,plain,(
% 3.13/0.80    spl11_2 <=> sK1 = sK5),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 3.13/0.80  fof(f4591,plain,(
% 3.13/0.80    spl11_171 <=> sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_171])])).
% 3.13/0.80  fof(f5232,plain,(
% 3.13/0.80    sK1 = sK5 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_171),
% 3.13/0.80    inference(superposition,[],[f152,f4592])).
% 3.13/0.80  fof(f4592,plain,(
% 3.13/0.80    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl11_171),
% 3.13/0.80    inference(avatar_component_clause,[],[f4591])).
% 3.13/0.80  fof(f152,plain,(
% 3.13/0.80    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/0.80    inference(cnf_transformation,[],[f61])).
% 3.13/0.80  fof(f61,plain,(
% 3.13/0.80    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.13/0.80    inference(ennf_transformation,[],[f35])).
% 3.13/0.80  fof(f35,axiom,(
% 3.13/0.80    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.13/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 3.13/0.80  fof(f4766,plain,(
% 3.13/0.80    ~spl11_186 | spl11_1 | ~spl11_170),
% 3.13/0.80    inference(avatar_split_clause,[],[f4761,f4587,f232,f4672])).
% 3.13/0.80  fof(f4672,plain,(
% 3.13/0.80    spl11_186 <=> r1_tarski(sK0,sK4)),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_186])])).
% 3.13/0.80  fof(f232,plain,(
% 3.13/0.80    spl11_1 <=> sK0 = sK4),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 3.13/0.80  fof(f4587,plain,(
% 3.13/0.80    spl11_170 <=> sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_170])])).
% 3.13/0.80  fof(f4761,plain,(
% 3.13/0.80    sK0 = sK4 | ~r1_tarski(sK0,sK4) | ~spl11_170),
% 3.13/0.80    inference(resolution,[],[f4752,f134])).
% 3.13/0.80  fof(f134,plain,(
% 3.13/0.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.13/0.80    inference(cnf_transformation,[],[f79])).
% 3.13/0.80  fof(f79,plain,(
% 3.13/0.80    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/0.80    inference(flattening,[],[f78])).
% 3.13/0.80  fof(f78,plain,(
% 3.13/0.80    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/0.80    inference(nnf_transformation,[],[f7])).
% 3.13/0.80  fof(f7,axiom,(
% 3.13/0.80    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.13/0.80  fof(f4752,plain,(
% 3.13/0.80    r1_tarski(sK4,sK0) | ~spl11_170),
% 3.13/0.80    inference(superposition,[],[f116,f4588])).
% 3.13/0.80  fof(f4588,plain,(
% 3.13/0.80    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl11_170),
% 3.13/0.80    inference(avatar_component_clause,[],[f4587])).
% 3.13/0.80  fof(f116,plain,(
% 3.13/0.80    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 3.13/0.80    inference(cnf_transformation,[],[f33])).
% 3.13/0.80  fof(f33,axiom,(
% 3.13/0.80    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 3.13/0.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 3.13/0.80  fof(f4674,plain,(
% 3.13/0.80    spl11_31 | spl11_32 | spl11_186 | ~spl11_14),
% 3.13/0.80    inference(avatar_split_clause,[],[f4666,f341,f4672,f488,f485])).
% 3.13/0.80  fof(f341,plain,(
% 3.13/0.80    spl11_14 <=> ! [X32,X31,X33] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33) | k2_zfmisc_1(sK4,sK5) = X31)),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 3.13/0.80  fof(f4666,plain,(
% 3.13/0.80    r1_tarski(sK0,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_14),
% 3.13/0.80    inference(superposition,[],[f4534,f151])).
% 3.13/0.80  fof(f151,plain,(
% 3.13/0.80    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/0.80    inference(cnf_transformation,[],[f61])).
% 3.13/0.80  fof(f4534,plain,(
% 3.13/0.80    r1_tarski(k1_relat_1(k2_zfmisc_1(sK0,sK1)),sK4) | ~spl11_14),
% 3.13/0.80    inference(superposition,[],[f116,f4486])).
% 3.13/0.80  fof(f4486,plain,(
% 3.13/0.80    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) | ~spl11_14),
% 3.13/0.80    inference(equality_resolution,[],[f342])).
% 3.13/0.80  fof(f342,plain,(
% 3.13/0.80    ( ! [X33,X31,X32] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33) | k2_zfmisc_1(sK4,sK5) = X31) ) | ~spl11_14),
% 3.13/0.80    inference(avatar_component_clause,[],[f341])).
% 3.13/0.80  fof(f4593,plain,(
% 3.13/0.80    spl11_5 | spl11_6 | spl11_171 | ~spl11_14),
% 3.13/0.80    inference(avatar_split_clause,[],[f4539,f341,f4591,f312,f309])).
% 3.13/0.80  fof(f309,plain,(
% 3.13/0.80    spl11_5 <=> k1_xboole_0 = sK4),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 3.13/0.80  fof(f312,plain,(
% 3.13/0.80    spl11_6 <=> k1_xboole_0 = sK5),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 3.13/0.80  fof(f4539,plain,(
% 3.13/0.80    sK5 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl11_14),
% 3.13/0.80    inference(superposition,[],[f152,f4486])).
% 3.13/0.80  fof(f4589,plain,(
% 3.13/0.80    spl11_5 | spl11_6 | spl11_170 | ~spl11_14),
% 3.13/0.80    inference(avatar_split_clause,[],[f4538,f341,f4587,f312,f309])).
% 3.13/0.80  fof(f4538,plain,(
% 3.13/0.80    sK4 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl11_14),
% 3.13/0.80    inference(superposition,[],[f151,f4486])).
% 3.13/0.80  fof(f2479,plain,(
% 3.13/0.80    ~spl11_95 | spl11_4 | ~spl11_22),
% 3.13/0.80    inference(avatar_split_clause,[],[f2475,f378,f241,f2450])).
% 3.13/0.80  fof(f2450,plain,(
% 3.13/0.80    spl11_95 <=> r1_tarski(sK3,sK7)),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_95])])).
% 3.13/0.80  fof(f241,plain,(
% 3.13/0.80    spl11_4 <=> sK3 = sK7),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 3.13/0.80  fof(f378,plain,(
% 3.13/0.80    spl11_22 <=> sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 3.13/0.80    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 3.13/0.80  fof(f2475,plain,(
% 3.13/0.80    sK3 = sK7 | ~r1_tarski(sK3,sK7) | ~spl11_22),
% 3.13/0.80    inference(resolution,[],[f2456,f134])).
% 3.13/0.80  fof(f2456,plain,(
% 3.13/0.80    r1_tarski(sK7,sK3) | ~spl11_22),
% 3.13/0.80    inference(superposition,[],[f115,f379])).
% 3.13/0.80  fof(f379,plain,(
% 3.13/0.80    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl11_22),
% 3.13/0.80    inference(avatar_component_clause,[],[f378])).
% 3.13/0.82  fof(f115,plain,(
% 3.13/0.82    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f34])).
% 3.13/0.82  fof(f34,axiom,(
% 3.13/0.82    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 3.13/0.82  fof(f2452,plain,(
% 3.13/0.82    spl11_45 | spl11_95),
% 3.13/0.82    inference(avatar_split_clause,[],[f2448,f2450,f541])).
% 3.13/0.82  fof(f541,plain,(
% 3.13/0.82    spl11_45 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 3.13/0.82  fof(f2448,plain,(
% 3.13/0.82    r1_tarski(sK3,sK7) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 3.13/0.82    inference(global_subsumption,[],[f101,f2443])).
% 3.13/0.82  fof(f2443,plain,(
% 3.13/0.82    r1_tarski(sK3,sK7) | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 3.13/0.82    inference(superposition,[],[f270,f152])).
% 3.13/0.82  fof(f270,plain,(
% 3.13/0.82    r1_tarski(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),sK7)),
% 3.13/0.82    inference(superposition,[],[f115,f185])).
% 3.13/0.82  fof(f185,plain,(
% 3.13/0.82    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 3.13/0.82    inference(definition_unfolding,[],[f97,f168,f168])).
% 3.13/0.82  fof(f168,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f43])).
% 3.13/0.82  fof(f43,axiom,(
% 3.13/0.82    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 3.13/0.82  fof(f97,plain,(
% 3.13/0.82    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  fof(f71,plain,(
% 3.13/0.82    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 3.13/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f49,f70])).
% 3.13/0.82  fof(f70,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 3.13/0.82    introduced(choice_axiom,[])).
% 3.13/0.82  fof(f49,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.13/0.82    inference(flattening,[],[f48])).
% 3.13/0.82  fof(f48,plain,(
% 3.13/0.82    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 3.13/0.82    inference(ennf_transformation,[],[f46])).
% 3.13/0.82  fof(f46,negated_conjecture,(
% 3.13/0.82    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    inference(negated_conjecture,[],[f45])).
% 3.13/0.82  fof(f45,conjecture,(
% 3.13/0.82    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 3.13/0.82  fof(f101,plain,(
% 3.13/0.82    k1_xboole_0 != sK3),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  fof(f2426,plain,(
% 3.13/0.82    spl11_20 | spl11_8 | spl11_22),
% 3.13/0.82    inference(avatar_split_clause,[],[f2380,f378,f318,f370])).
% 3.13/0.82  fof(f370,plain,(
% 3.13/0.82    spl11_20 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 3.13/0.82  fof(f318,plain,(
% 3.13/0.82    spl11_8 <=> k1_xboole_0 = sK7),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 3.13/0.82  fof(f2380,plain,(
% 3.13/0.82    sK7 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)),
% 3.13/0.82    inference(superposition,[],[f152,f185])).
% 3.13/0.82  fof(f2417,plain,(
% 3.13/0.82    spl11_10 | spl11_7 | spl11_8 | spl11_14),
% 3.13/0.82    inference(avatar_split_clause,[],[f2361,f341,f318,f315,f325])).
% 3.13/0.82  fof(f325,plain,(
% 3.13/0.82    spl11_10 <=> k1_xboole_0 = k2_zfmisc_1(sK4,sK5)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 3.13/0.82  fof(f315,plain,(
% 3.13/0.82    spl11_7 <=> k1_xboole_0 = sK6),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 3.13/0.82  fof(f2361,plain,(
% 3.13/0.82    ( ! [X33,X31,X32] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X31,X32),X33) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | k2_zfmisc_1(sK4,sK5) = X31) )),
% 3.13/0.82    inference(superposition,[],[f215,f185])).
% 3.13/0.82  fof(f215,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X3) )),
% 3.13/0.82    inference(definition_unfolding,[],[f177,f154,f154])).
% 3.13/0.82  fof(f154,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f38])).
% 3.13/0.82  fof(f38,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 3.13/0.82  fof(f177,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f67])).
% 3.13/0.82  fof(f67,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.13/0.82    inference(flattening,[],[f66])).
% 3.13/0.82  fof(f66,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 3.13/0.82    inference(ennf_transformation,[],[f40])).
% 3.13/0.82  fof(f40,axiom,(
% 3.13/0.82    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).
% 3.13/0.82  fof(f2416,plain,(
% 3.13/0.82    spl11_10 | spl11_7 | spl11_8 | spl11_13),
% 3.13/0.82    inference(avatar_split_clause,[],[f2359,f337,f318,f315,f325])).
% 3.13/0.82  fof(f2359,plain,(
% 3.13/0.82    ( ! [X26,X27,X25] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27) | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | sK6 = X26) )),
% 3.13/0.82    inference(superposition,[],[f214,f185])).
% 3.13/0.82  fof(f214,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X4) )),
% 3.13/0.82    inference(definition_unfolding,[],[f178,f154,f154])).
% 3.13/0.82  fof(f178,plain,(
% 3.13/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (X1 = X4 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f67])).
% 3.13/0.82  fof(f2308,plain,(
% 3.13/0.82    spl11_35 | spl11_33 | ~spl11_45),
% 3.13/0.82    inference(avatar_split_clause,[],[f2307,f541,f491,f498])).
% 3.13/0.82  fof(f498,plain,(
% 3.13/0.82    spl11_35 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 3.13/0.82  fof(f491,plain,(
% 3.13/0.82    spl11_33 <=> k1_xboole_0 = sK2),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 3.13/0.82  fof(f2307,plain,(
% 3.13/0.82    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_45),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f2306])).
% 3.13/0.82  fof(f2306,plain,(
% 3.13/0.82    k1_xboole_0 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_45),
% 3.13/0.82    inference(forward_demodulation,[],[f2247,f104])).
% 3.13/0.82  fof(f104,plain,(
% 3.13/0.82    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.13/0.82    inference(cnf_transformation,[],[f36])).
% 3.13/0.82  fof(f36,axiom,(
% 3.13/0.82    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 3.13/0.82  fof(f2247,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_45),
% 3.13/0.82    inference(superposition,[],[f152,f542])).
% 3.13/0.82  fof(f542,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_45),
% 3.13/0.82    inference(avatar_component_clause,[],[f541])).
% 3.13/0.82  fof(f2170,plain,(
% 3.13/0.82    spl11_10 | spl11_7 | ~spl11_20),
% 3.13/0.82    inference(avatar_split_clause,[],[f2169,f370,f315,f325])).
% 3.13/0.82  fof(f2169,plain,(
% 3.13/0.82    k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl11_20),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f2168])).
% 3.13/0.82  fof(f2168,plain,(
% 3.13/0.82    k1_xboole_0 = sK6 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl11_20),
% 3.13/0.82    inference(forward_demodulation,[],[f2108,f104])).
% 3.13/0.82  fof(f2108,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK6 | k1_xboole_0 = sK6 | k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl11_20),
% 3.13/0.82    inference(superposition,[],[f152,f371])).
% 3.13/0.82  fof(f371,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6) | ~spl11_20),
% 3.13/0.82    inference(avatar_component_clause,[],[f370])).
% 3.13/0.82  fof(f1924,plain,(
% 3.13/0.82    spl11_31 | spl11_32 | ~spl11_35),
% 3.13/0.82    inference(avatar_split_clause,[],[f1923,f498,f488,f485])).
% 3.13/0.82  fof(f1923,plain,(
% 3.13/0.82    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_35),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f1922])).
% 3.13/0.82  fof(f1922,plain,(
% 3.13/0.82    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_35),
% 3.13/0.82    inference(forward_demodulation,[],[f1865,f104])).
% 3.13/0.82  fof(f1865,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl11_35),
% 3.13/0.82    inference(superposition,[],[f152,f499])).
% 3.13/0.82  fof(f499,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl11_35),
% 3.13/0.82    inference(avatar_component_clause,[],[f498])).
% 3.13/0.82  fof(f1764,plain,(
% 3.13/0.82    ~spl11_32),
% 3.13/0.82    inference(avatar_contradiction_clause,[],[f1762])).
% 3.13/0.82  fof(f1762,plain,(
% 3.13/0.82    $false | ~spl11_32),
% 3.13/0.82    inference(subsumption_resolution,[],[f99,f489])).
% 3.13/0.82  fof(f489,plain,(
% 3.13/0.82    k1_xboole_0 = sK1 | ~spl11_32),
% 3.13/0.82    inference(avatar_component_clause,[],[f488])).
% 3.13/0.82  fof(f99,plain,(
% 3.13/0.82    k1_xboole_0 != sK1),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  fof(f1734,plain,(
% 3.13/0.82    spl11_45 | spl11_34 | ~spl11_8),
% 3.13/0.82    inference(avatar_split_clause,[],[f1733,f318,f494,f541])).
% 3.13/0.82  fof(f494,plain,(
% 3.13/0.82    spl11_34 <=> k1_xboole_0 = sK3),
% 3.13/0.82    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 3.13/0.82  fof(f1733,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_8),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f1732])).
% 3.13/0.82  fof(f1732,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_8),
% 3.13/0.82    inference(forward_demodulation,[],[f1683,f104])).
% 3.13/0.82  fof(f1683,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_8),
% 3.13/0.82    inference(superposition,[],[f152,f1421])).
% 3.13/0.82  fof(f1421,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl11_8),
% 3.13/0.82    inference(forward_demodulation,[],[f1419,f222])).
% 3.13/0.82  fof(f222,plain,(
% 3.13/0.82    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.13/0.82    inference(equality_resolution,[],[f146])).
% 3.13/0.82  fof(f146,plain,(
% 3.13/0.82    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.13/0.82    inference(cnf_transformation,[],[f88])).
% 3.13/0.82  fof(f88,plain,(
% 3.13/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/0.82    inference(flattening,[],[f87])).
% 3.13/0.82  fof(f87,plain,(
% 3.13/0.82    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.13/0.82    inference(nnf_transformation,[],[f27])).
% 3.13/0.82  fof(f27,axiom,(
% 3.13/0.82    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.13/0.82  fof(f1419,plain,(
% 3.13/0.82    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k1_xboole_0) | ~spl11_8),
% 3.13/0.82    inference(backward_demodulation,[],[f185,f319])).
% 3.13/0.82  fof(f319,plain,(
% 3.13/0.82    k1_xboole_0 = sK7 | ~spl11_8),
% 3.13/0.82    inference(avatar_component_clause,[],[f318])).
% 3.13/0.82  fof(f1650,plain,(
% 3.13/0.82    ~spl11_31),
% 3.13/0.82    inference(avatar_contradiction_clause,[],[f1647])).
% 3.13/0.82  fof(f1647,plain,(
% 3.13/0.82    $false | ~spl11_31),
% 3.13/0.82    inference(subsumption_resolution,[],[f98,f486])).
% 3.13/0.82  fof(f486,plain,(
% 3.13/0.82    k1_xboole_0 = sK0 | ~spl11_31),
% 3.13/0.82    inference(avatar_component_clause,[],[f485])).
% 3.13/0.82  fof(f98,plain,(
% 3.13/0.82    k1_xboole_0 != sK0),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  fof(f1535,plain,(
% 3.13/0.82    ~spl11_33),
% 3.13/0.82    inference(avatar_contradiction_clause,[],[f1533])).
% 3.13/0.82  fof(f1533,plain,(
% 3.13/0.82    $false | ~spl11_33),
% 3.13/0.82    inference(subsumption_resolution,[],[f100,f492])).
% 3.13/0.82  fof(f492,plain,(
% 3.13/0.82    k1_xboole_0 = sK2 | ~spl11_33),
% 3.13/0.82    inference(avatar_component_clause,[],[f491])).
% 3.13/0.82  fof(f100,plain,(
% 3.13/0.82    k1_xboole_0 != sK2),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  fof(f1285,plain,(
% 3.13/0.82    spl11_5 | spl11_6 | ~spl11_10),
% 3.13/0.82    inference(avatar_split_clause,[],[f1284,f325,f312,f309])).
% 3.13/0.82  fof(f1284,plain,(
% 3.13/0.82    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl11_10),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f1283])).
% 3.13/0.82  fof(f1283,plain,(
% 3.13/0.82    k1_xboole_0 = sK5 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl11_10),
% 3.13/0.82    inference(forward_demodulation,[],[f1226,f104])).
% 3.13/0.82  fof(f1226,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK5 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | ~spl11_10),
% 3.13/0.82    inference(superposition,[],[f152,f326])).
% 3.13/0.82  fof(f326,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(sK4,sK5) | ~spl11_10),
% 3.13/0.82    inference(avatar_component_clause,[],[f325])).
% 3.13/0.82  fof(f1099,plain,(
% 3.13/0.82    spl11_45 | spl11_34 | ~spl11_6),
% 3.13/0.82    inference(avatar_split_clause,[],[f1098,f312,f494,f541])).
% 3.13/0.82  fof(f1098,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_6),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f1097])).
% 3.13/0.82  fof(f1097,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_6),
% 3.13/0.82    inference(forward_demodulation,[],[f1047,f104])).
% 3.13/0.82  fof(f1047,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_6),
% 3.13/0.82    inference(superposition,[],[f152,f1014])).
% 3.13/0.82  fof(f1014,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl11_6),
% 3.13/0.82    inference(forward_demodulation,[],[f1013,f229])).
% 3.13/0.82  fof(f229,plain,(
% 3.13/0.82    ( ! [X2,X0,X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3)) )),
% 3.13/0.82    inference(equality_resolution,[],[f207])).
% 3.13/0.82  fof(f207,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.13/0.82    inference(definition_unfolding,[],[f171,f168])).
% 3.13/0.82  fof(f171,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f96])).
% 3.13/0.82  fof(f96,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    inference(flattening,[],[f95])).
% 3.13/0.82  fof(f95,plain,(
% 3.13/0.82    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.13/0.82    inference(nnf_transformation,[],[f44])).
% 3.13/0.82  fof(f44,axiom,(
% 3.13/0.82    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 3.13/0.82  fof(f1013,plain,(
% 3.13/0.82    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0),sK6),sK7) | ~spl11_6),
% 3.13/0.82    inference(backward_demodulation,[],[f185,f313])).
% 3.13/0.82  fof(f313,plain,(
% 3.13/0.82    k1_xboole_0 = sK5 | ~spl11_6),
% 3.13/0.82    inference(avatar_component_clause,[],[f312])).
% 3.13/0.82  fof(f924,plain,(
% 3.13/0.82    ~spl11_34),
% 3.13/0.82    inference(avatar_contradiction_clause,[],[f921])).
% 3.13/0.82  fof(f921,plain,(
% 3.13/0.82    $false | ~spl11_34),
% 3.13/0.82    inference(subsumption_resolution,[],[f101,f495])).
% 3.13/0.82  fof(f495,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | ~spl11_34),
% 3.13/0.82    inference(avatar_component_clause,[],[f494])).
% 3.13/0.82  fof(f893,plain,(
% 3.13/0.82    spl11_45 | spl11_34 | ~spl11_5),
% 3.13/0.82    inference(avatar_split_clause,[],[f892,f309,f494,f541])).
% 3.13/0.82  fof(f892,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_5),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f891])).
% 3.13/0.82  fof(f891,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_5),
% 3.13/0.82    inference(forward_demodulation,[],[f840,f104])).
% 3.13/0.82  fof(f840,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_5),
% 3.13/0.82    inference(superposition,[],[f152,f807])).
% 3.13/0.82  fof(f807,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl11_5),
% 3.13/0.82    inference(forward_demodulation,[],[f806,f230])).
% 3.13/0.82  fof(f230,plain,(
% 3.13/0.82    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.13/0.82    inference(equality_resolution,[],[f208])).
% 3.13/0.82  fof(f208,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.13/0.82    inference(definition_unfolding,[],[f170,f168])).
% 3.13/0.82  fof(f170,plain,(
% 3.13/0.82    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f96])).
% 3.13/0.82  fof(f806,plain,(
% 3.13/0.82    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5),sK6),sK7) | ~spl11_5),
% 3.13/0.82    inference(forward_demodulation,[],[f185,f310])).
% 3.13/0.82  fof(f310,plain,(
% 3.13/0.82    k1_xboole_0 = sK4 | ~spl11_5),
% 3.13/0.82    inference(avatar_component_clause,[],[f309])).
% 3.13/0.82  fof(f777,plain,(
% 3.13/0.82    spl11_45 | spl11_34 | ~spl11_7),
% 3.13/0.82    inference(avatar_split_clause,[],[f776,f315,f494,f541])).
% 3.13/0.82  fof(f776,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_7),
% 3.13/0.82    inference(duplicate_literal_removal,[],[f775])).
% 3.13/0.82  fof(f775,plain,(
% 3.13/0.82    k1_xboole_0 = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_7),
% 3.13/0.82    inference(forward_demodulation,[],[f724,f104])).
% 3.13/0.82  fof(f724,plain,(
% 3.13/0.82    k2_relat_1(k1_xboole_0) = sK3 | k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl11_7),
% 3.13/0.82    inference(superposition,[],[f152,f691])).
% 3.13/0.82  fof(f691,plain,(
% 3.13/0.82    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | ~spl11_7),
% 3.13/0.82    inference(forward_demodulation,[],[f690,f225])).
% 3.13/0.82  fof(f225,plain,(
% 3.13/0.82    ( ! [X2,X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2)) )),
% 3.13/0.82    inference(equality_resolution,[],[f202])).
% 3.13/0.82  fof(f202,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.13/0.82    inference(definition_unfolding,[],[f164,f154])).
% 3.13/0.82  fof(f164,plain,(
% 3.13/0.82    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 3.13/0.82    inference(cnf_transformation,[],[f94])).
% 3.13/0.82  fof(f94,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/0.82    inference(flattening,[],[f93])).
% 3.13/0.82  fof(f93,plain,(
% 3.13/0.82    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.13/0.82    inference(nnf_transformation,[],[f39])).
% 3.13/0.82  fof(f39,axiom,(
% 3.13/0.82    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 3.13/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).
% 3.13/0.82  fof(f690,plain,(
% 3.13/0.82    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),k1_xboole_0),sK7) | ~spl11_7),
% 3.13/0.82    inference(backward_demodulation,[],[f185,f316])).
% 3.13/0.82  fof(f316,plain,(
% 3.13/0.82    k1_xboole_0 = sK6 | ~spl11_7),
% 3.13/0.82    inference(avatar_component_clause,[],[f315])).
% 3.13/0.82  fof(f243,plain,(
% 3.13/0.82    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4),
% 3.13/0.82    inference(avatar_split_clause,[],[f102,f241,f238,f235,f232])).
% 3.13/0.82  fof(f102,plain,(
% 3.13/0.82    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 3.13/0.82    inference(cnf_transformation,[],[f71])).
% 3.13/0.82  % SZS output end Proof for theBenchmark
% 3.13/0.82  % (30731)------------------------------
% 3.13/0.82  % (30731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (30731)Termination reason: Refutation
% 3.13/0.82  
% 3.13/0.82  % (30731)Memory used [KB]: 13304
% 3.13/0.82  % (30731)Time elapsed: 0.379 s
% 3.13/0.82  % (30731)------------------------------
% 3.13/0.82  % (30731)------------------------------
% 3.13/0.82  % (30728)Success in time 0.458 s
%------------------------------------------------------------------------------
