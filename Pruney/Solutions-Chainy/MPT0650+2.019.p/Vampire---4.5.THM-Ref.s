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
% DateTime   : Thu Dec  3 12:52:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 396 expanded)
%              Number of leaves         :   50 ( 179 expanded)
%              Depth                    :    9
%              Number of atoms          :  647 (1420 expanded)
%              Number of equality atoms :  126 ( 283 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f938,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f110,f122,f153,f161,f163,f182,f214,f225,f256,f265,f273,f308,f311,f404,f415,f417,f475,f588,f606,f610,f622,f624,f635,f926,f936,f937])).

fof(f937,plain,
    ( k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) != k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))))
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | k2_funct_1(sK1) != k4_relat_1(sK1)
    | sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))
    | k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f936,plain,
    ( ~ spl5_46
    | ~ spl5_74
    | ~ spl5_75
    | spl5_76
    | ~ spl5_105 ),
    inference(avatar_split_clause,[],[f935,f924,f633,f626,f620,f413])).

fof(f413,plain,
    ( spl5_46
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f620,plain,
    ( spl5_74
  <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f626,plain,
    ( spl5_75
  <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f633,plain,
    ( spl5_76
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f924,plain,
    ( spl5_105
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))
        | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f935,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_74
    | ~ spl5_75
    | spl5_76
    | ~ spl5_105 ),
    inference(trivial_inequality_removal,[],[f934])).

fof(f934,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_74
    | ~ spl5_75
    | spl5_76
    | ~ spl5_105 ),
    inference(forward_demodulation,[],[f933,f621])).

fof(f621,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f620])).

fof(f933,plain,
    ( sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_75
    | spl5_76
    | ~ spl5_105 ),
    inference(forward_demodulation,[],[f931,f627])).

fof(f627,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f626])).

fof(f931,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl5_76
    | ~ spl5_105 ),
    inference(superposition,[],[f634,f925])).

fof(f925,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0)
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f924])).

fof(f634,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_76 ),
    inference(avatar_component_clause,[],[f633])).

fof(f926,plain,
    ( ~ spl5_6
    | spl5_105
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f922,f473,f222,f92,f924,f96])).

fof(f96,plain,
    ( spl5_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f92,plain,
    ( spl5_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f222,plain,
    ( spl5_17
  <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f473,plain,
    ( spl5_54
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f922,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) )
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f919,f223])).

fof(f223,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f222])).

fof(f919,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
        | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) )
    | ~ spl5_5
    | ~ spl5_54 ),
    inference(resolution,[],[f474,f93])).

fof(f93,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f474,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f473])).

fof(f635,plain,
    ( ~ spl5_76
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f631,f108,f80,f633])).

fof(f80,plain,
    ( spl5_2
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( spl5_7
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f631,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f81,f109])).

fof(f109,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f81,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f624,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK0)) != k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0))))
    | sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))
    | k2_funct_1(sK1) != k4_relat_1(sK1)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f622,plain,
    ( spl5_74
    | ~ spl5_3
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f600,f586,f84,f620])).

fof(f84,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f586,plain,
    ( spl5_68
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f600,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_3
    | ~ spl5_68 ),
    inference(resolution,[],[f587,f85])).

fof(f85,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f587,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK4(sK1,X0)) = X0 )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f586])).

fof(f610,plain,
    ( spl5_71
    | ~ spl5_31
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f597,f586,f303,f608])).

fof(f608,plain,
    ( spl5_71
  <=> k1_funct_1(sK1,sK4(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f303,plain,
    ( spl5_31
  <=> r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f597,plain,
    ( k1_funct_1(sK1,sK4(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0))))
    | ~ spl5_31
    | ~ spl5_68 ),
    inference(resolution,[],[f587,f329])).

fof(f329,plain,
    ( r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f303])).

fof(f606,plain,
    ( spl5_70
    | ~ spl5_45
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f596,f586,f399,f604])).

fof(f604,plain,
    ( spl5_70
  <=> k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f399,plain,
    ( spl5_45
  <=> r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f596,plain,
    ( k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))))
    | ~ spl5_45
    | ~ spl5_68 ),
    inference(resolution,[],[f587,f428])).

fof(f428,plain,
    ( r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f399])).

fof(f588,plain,
    ( ~ spl5_6
    | spl5_68
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f582,f92,f586,f96])).

fof(f582,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1,X0)) = X0
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f141,f93])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) = X1
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f475,plain,
    ( ~ spl5_11
    | spl5_54
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f466,f120,f473,f156])).

fof(f156,plain,
    ( spl5_11
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f120,plain,
    ( spl5_9
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f466,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6) )
    | ~ spl5_9 ),
    inference(resolution,[],[f63,f121])).

fof(f121,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f417,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_46 ),
    inference(avatar_split_clause,[],[f416,f413,f84,f96])).

fof(f416,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl5_46 ),
    inference(superposition,[],[f414,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f414,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl5_46 ),
    inference(avatar_component_clause,[],[f413])).

fof(f415,plain,
    ( ~ spl5_46
    | ~ spl5_14
    | spl5_42 ),
    inference(avatar_split_clause,[],[f411,f386,f180,f413])).

fof(f180,plain,
    ( spl5_14
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f386,plain,
    ( spl5_42
  <=> r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f411,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_14
    | spl5_42 ),
    inference(resolution,[],[f403,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f403,plain,
    ( ~ r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f386])).

fof(f404,plain,
    ( ~ spl5_42
    | ~ spl5_10
    | spl5_45 ),
    inference(avatar_split_clause,[],[f402,f399,f151,f386])).

fof(f151,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

% (32000)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f402,plain,
    ( ~ r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl5_10
    | spl5_45 ),
    inference(resolution,[],[f400,f174])).

fof(f174,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(sK1,X2),k2_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_10 ),
    inference(resolution,[],[f152,f73])).

fof(f73,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f400,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f399])).

fof(f311,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_26 ),
    inference(avatar_split_clause,[],[f309,f282,f84,f96])).

fof(f282,plain,
    ( spl5_26
  <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f309,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl5_26 ),
    inference(resolution,[],[f307,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f307,plain,
    ( ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f282])).

fof(f308,plain,
    ( ~ spl5_26
    | ~ spl5_10
    | spl5_31 ),
    inference(avatar_split_clause,[],[f306,f303,f151,f282])).

fof(f306,plain,
    ( ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_10
    | spl5_31 ),
    inference(resolution,[],[f304,f174])).

fof(f304,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f303])).

fof(f273,plain,
    ( spl5_24
    | ~ spl5_3
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f268,f263,f84,f271])).

fof(f271,plain,
    ( spl5_24
  <=> sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f263,plain,
    ( spl5_23
  <=> ! [X2] :
        ( sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2)))
        | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f268,plain,
    ( sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))
    | ~ spl5_3
    | ~ spl5_23 ),
    inference(resolution,[],[f264,f85])).

fof(f264,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2))) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( ~ spl5_6
    | spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f260,f254,f263,f96])).

fof(f254,plain,
    ( spl5_22
  <=> ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f260,plain,
    ( ! [X2] :
        ( sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2)))
        | ~ r2_hidden(X2,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_22 ),
    inference(resolution,[],[f255,f123])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f256,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | spl5_22
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f250,f108,f254,f88,f92,f96])).

fof(f88,plain,
    ( spl5_4
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f250,plain,
    ( ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v2_funct_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_7 ),
    inference(superposition,[],[f61,f109])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f225,plain,
    ( ~ spl5_11
    | ~ spl5_6
    | spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f220,f212,f222,f96,f156])).

fof(f212,plain,
    ( spl5_15
  <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f220,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl5_15 ),
    inference(superposition,[],[f57,f213])).

fof(f213,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f212])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f214,plain,
    ( ~ spl5_6
    | spl5_15
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f206,f96,f212,f96])).

fof(f206,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(superposition,[],[f205,f102])).

fof(f102,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f53,f100])).

fof(f100,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f54,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f205,plain,
    ( ! [X6] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X6))) = k10_relat_1(k4_relat_1(sK1),X6)
    | ~ spl5_6 ),
    inference(resolution,[],[f143,f97])).

fof(f97,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1) ) ),
    inference(resolution,[],[f142,f53])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1) ) ),
    inference(resolution,[],[f134,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f57,f51])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f182,plain,
    ( ~ spl5_6
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f178,f159,f180,f96])).

fof(f159,plain,
    ( spl5_12
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))
        | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f178,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_12 ),
    inference(superposition,[],[f177,f56])).

fof(f177,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k4_relat_1(sK1),X2),k2_relat_1(k4_relat_1(sK1)))
        | ~ r2_hidden(X2,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_12 ),
    inference(resolution,[],[f160,f73])).

fof(f160,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f163,plain,
    ( ~ spl5_6
    | spl5_11 ),
    inference(avatar_split_clause,[],[f162,f156,f96])).

fof(f162,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_11 ),
    inference(resolution,[],[f157,f53])).

fof(f157,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f161,plain,
    ( ~ spl5_11
    | spl5_12
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f149,f120,f159,f156])).

fof(f149,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))
        | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f75,f121])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f153,plain,
    ( ~ spl5_6
    | spl5_10
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f147,f92,f151,f96])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f75,f93])).

fof(f122,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f113,f108,f120,f92,f96])).

fof(f113,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f59,f109])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f110,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f103,f88,f108,f92,f96])).

fof(f103,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f60,f89])).

fof(f89,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f98,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
      | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
    & r2_hidden(sK0,k2_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
        | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
      & r2_hidden(sK0,k2_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f94,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f80,f77])).

fof(f77,plain,
    ( spl5_1
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (31996)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (31988)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (31999)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (31992)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (31980)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (31994)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (31990)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (31993)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (31981)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (31983)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (31981)Refutation not found, incomplete strategy% (31981)------------------------------
% 0.20/0.49  % (31981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31981)Memory used [KB]: 10618
% 0.20/0.49  % (31981)Time elapsed: 0.082 s
% 0.20/0.49  % (31981)------------------------------
% 0.20/0.49  % (31981)------------------------------
% 0.20/0.49  % (32002)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (32002)Refutation not found, incomplete strategy% (32002)------------------------------
% 0.20/0.49  % (32002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (32002)Memory used [KB]: 10618
% 0.20/0.49  % (32002)Time elapsed: 0.086 s
% 0.20/0.49  % (32002)------------------------------
% 0.20/0.49  % (32002)------------------------------
% 0.20/0.50  % (31986)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (31985)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (31998)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (31984)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (31989)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (31995)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (31991)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (31997)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (31988)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f938,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f110,f122,f153,f161,f163,f182,f214,f225,f256,f265,f273,f308,f311,f404,f415,f417,f475,f588,f606,f610,f622,f624,f635,f926,f936,f937])).
% 0.20/0.51  fof(f937,plain,(
% 0.20/0.51    k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) != k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)))) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | k2_funct_1(sK1) != k4_relat_1(sK1) | sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) | k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f936,plain,(
% 0.20/0.51    ~spl5_46 | ~spl5_74 | ~spl5_75 | spl5_76 | ~spl5_105),
% 0.20/0.51    inference(avatar_split_clause,[],[f935,f924,f633,f626,f620,f413])).
% 0.20/0.51  fof(f413,plain,(
% 0.20/0.51    spl5_46 <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.20/0.51  fof(f620,plain,(
% 0.20/0.51    spl5_74 <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.20/0.51  fof(f626,plain,(
% 0.20/0.51    spl5_75 <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 0.20/0.51  fof(f633,plain,(
% 0.20/0.51    spl5_76 <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.20/0.51  fof(f924,plain,(
% 0.20/0.51    spl5_105 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 0.20/0.51  fof(f935,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_74 | ~spl5_75 | spl5_76 | ~spl5_105)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f934])).
% 0.20/0.51  fof(f934,plain,(
% 0.20/0.51    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_74 | ~spl5_75 | spl5_76 | ~spl5_105)),
% 0.20/0.51    inference(forward_demodulation,[],[f933,f621])).
% 0.20/0.51  fof(f621,plain,(
% 0.20/0.51    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_74),
% 0.20/0.51    inference(avatar_component_clause,[],[f620])).
% 0.20/0.51  fof(f933,plain,(
% 0.20/0.51    sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_75 | spl5_76 | ~spl5_105)),
% 0.20/0.51    inference(forward_demodulation,[],[f931,f627])).
% 0.20/0.51  fof(f627,plain,(
% 0.20/0.51    k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) | ~spl5_75),
% 0.20/0.51    inference(avatar_component_clause,[],[f626])).
% 0.20/0.51  fof(f931,plain,(
% 0.20/0.51    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (spl5_76 | ~spl5_105)),
% 0.20/0.51    inference(superposition,[],[f634,f925])).
% 0.20/0.51  fof(f925,plain,(
% 0.20/0.51    ( ! [X0] : (k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_105),
% 0.20/0.51    inference(avatar_component_clause,[],[f924])).
% 0.20/0.51  fof(f634,plain,(
% 0.20/0.51    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | spl5_76),
% 0.20/0.51    inference(avatar_component_clause,[],[f633])).
% 0.20/0.51  fof(f926,plain,(
% 0.20/0.51    ~spl5_6 | spl5_105 | ~spl5_5 | ~spl5_17 | ~spl5_54),
% 0.20/0.51    inference(avatar_split_clause,[],[f922,f473,f222,f92,f924,f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl5_6 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl5_5 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    spl5_17 <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.51  fof(f473,plain,(
% 0.20/0.51    spl5_54 <=> ! [X5,X6] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.20/0.51  fof(f922,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0)) ) | (~spl5_5 | ~spl5_17 | ~spl5_54)),
% 0.20/0.51    inference(forward_demodulation,[],[f919,f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | ~spl5_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f222])).
% 0.20/0.51  fof(f919,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0)) ) | (~spl5_5 | ~spl5_54)),
% 0.20/0.51    inference(resolution,[],[f474,f93])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    v1_funct_1(sK1) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f92])).
% 0.20/0.51  fof(f474,plain,(
% 0.20/0.51    ( ! [X6,X5] : (~v1_funct_1(X6) | ~v1_relat_1(X6) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5))) ) | ~spl5_54),
% 0.20/0.51    inference(avatar_component_clause,[],[f473])).
% 0.20/0.51  fof(f635,plain,(
% 0.20/0.51    ~spl5_76 | spl5_2 | ~spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f631,f108,f80,f633])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl5_2 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl5_7 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f631,plain,(
% 0.20/0.51    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | (spl5_2 | ~spl5_7)),
% 0.20/0.51    inference(forward_demodulation,[],[f81,f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f624,plain,(
% 0.20/0.51    k1_funct_1(sK1,sK4(sK1,sK0)) != k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0)))) | sK4(sK1,sK0) != k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) | k2_funct_1(sK1) != k4_relat_1(sK1) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 1.27/0.51  fof(f622,plain,(
% 1.27/0.51    spl5_74 | ~spl5_3 | ~spl5_68),
% 1.27/0.51    inference(avatar_split_clause,[],[f600,f586,f84,f620])).
% 1.27/0.51  fof(f84,plain,(
% 1.27/0.51    spl5_3 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.27/0.51  fof(f586,plain,(
% 1.27/0.51    spl5_68 <=> ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 1.27/0.51  fof(f600,plain,(
% 1.27/0.51    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | (~spl5_3 | ~spl5_68)),
% 1.27/0.51    inference(resolution,[],[f587,f85])).
% 1.27/0.51  fof(f85,plain,(
% 1.27/0.51    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_3),
% 1.27/0.51    inference(avatar_component_clause,[],[f84])).
% 1.27/0.51  fof(f587,plain,(
% 1.27/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,X0)) = X0) ) | ~spl5_68),
% 1.27/0.51    inference(avatar_component_clause,[],[f586])).
% 1.27/0.51  fof(f610,plain,(
% 1.27/0.51    spl5_71 | ~spl5_31 | ~spl5_68),
% 1.27/0.51    inference(avatar_split_clause,[],[f597,f586,f303,f608])).
% 1.27/0.51  fof(f608,plain,(
% 1.27/0.51    spl5_71 <=> k1_funct_1(sK1,sK4(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0))))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 1.27/0.51  fof(f303,plain,(
% 1.27/0.51    spl5_31 <=> r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.27/0.51  fof(f597,plain,(
% 1.27/0.51    k1_funct_1(sK1,sK4(sK1,sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK0)))) | (~spl5_31 | ~spl5_68)),
% 1.27/0.51    inference(resolution,[],[f587,f329])).
% 1.27/0.51  fof(f329,plain,(
% 1.27/0.51    r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1)) | ~spl5_31),
% 1.27/0.51    inference(avatar_component_clause,[],[f303])).
% 1.27/0.51  fof(f606,plain,(
% 1.27/0.51    spl5_70 | ~spl5_45 | ~spl5_68),
% 1.27/0.51    inference(avatar_split_clause,[],[f596,f586,f399,f604])).
% 1.27/0.51  fof(f604,plain,(
% 1.27/0.51    spl5_70 <=> k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 1.27/0.51  fof(f399,plain,(
% 1.27/0.51    spl5_45 <=> r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.27/0.51  fof(f596,plain,(
% 1.27/0.51    k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) = k1_funct_1(sK1,sK4(sK1,k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)))) | (~spl5_45 | ~spl5_68)),
% 1.27/0.51    inference(resolution,[],[f587,f428])).
% 1.27/0.51  fof(f428,plain,(
% 1.27/0.51    r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1)) | ~spl5_45),
% 1.27/0.51    inference(avatar_component_clause,[],[f399])).
% 1.27/0.51  fof(f588,plain,(
% 1.27/0.51    ~spl5_6 | spl5_68 | ~spl5_5),
% 1.27/0.51    inference(avatar_split_clause,[],[f582,f92,f586,f96])).
% 1.27/0.51  fof(f582,plain,(
% 1.27/0.51    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = X0 | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl5_5),
% 1.27/0.51    inference(resolution,[],[f141,f93])).
% 1.27/0.51  fof(f141,plain,(
% 1.27/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X1)) = X1 | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 1.27/0.51    inference(resolution,[],[f71,f74])).
% 1.27/0.51  fof(f74,plain,(
% 1.27/0.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.27/0.51    inference(equality_resolution,[],[f64])).
% 1.27/0.51  fof(f64,plain,(
% 1.27/0.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.27/0.51    inference(cnf_transformation,[],[f41])).
% 1.27/0.51  fof(f41,plain,(
% 1.27/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.27/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 1.27/0.51  fof(f38,plain,(
% 1.27/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.27/0.51    introduced(choice_axiom,[])).
% 1.27/0.51  fof(f39,plain,(
% 1.27/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 1.27/0.51    introduced(choice_axiom,[])).
% 1.27/0.51  fof(f40,plain,(
% 1.27/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 1.27/0.51    introduced(choice_axiom,[])).
% 1.27/0.51  fof(f37,plain,(
% 1.27/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.27/0.51    inference(rectify,[],[f36])).
% 1.27/0.51  fof(f36,plain,(
% 1.27/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.27/0.51    inference(nnf_transformation,[],[f1])).
% 1.27/0.51  fof(f1,axiom,(
% 1.27/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.27/0.51  fof(f71,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f43])).
% 1.27/0.51  fof(f43,plain,(
% 1.27/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.27/0.51    inference(flattening,[],[f42])).
% 1.27/0.51  fof(f42,plain,(
% 1.27/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.27/0.51    inference(nnf_transformation,[],[f33])).
% 1.27/0.51  fof(f33,plain,(
% 1.27/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.27/0.51    inference(flattening,[],[f32])).
% 1.27/0.51  fof(f32,plain,(
% 1.27/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.27/0.51    inference(ennf_transformation,[],[f13])).
% 1.27/0.51  fof(f13,axiom,(
% 1.27/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.27/0.51  fof(f475,plain,(
% 1.27/0.51    ~spl5_11 | spl5_54 | ~spl5_9),
% 1.27/0.51    inference(avatar_split_clause,[],[f466,f120,f473,f156])).
% 1.27/0.51  fof(f156,plain,(
% 1.27/0.51    spl5_11 <=> v1_relat_1(k4_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.27/0.51  fof(f120,plain,(
% 1.27/0.51    spl5_9 <=> v1_funct_1(k4_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.27/0.51  fof(f466,plain,(
% 1.27/0.51    ( ! [X6,X5] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) ) | ~spl5_9),
% 1.27/0.51    inference(resolution,[],[f63,f121])).
% 1.27/0.51  fof(f121,plain,(
% 1.27/0.51    v1_funct_1(k4_relat_1(sK1)) | ~spl5_9),
% 1.27/0.51    inference(avatar_component_clause,[],[f120])).
% 1.27/0.51  fof(f63,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f29])).
% 1.27/0.51  fof(f29,plain,(
% 1.27/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.27/0.51    inference(flattening,[],[f28])).
% 1.27/0.51  fof(f28,plain,(
% 1.27/0.51    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.27/0.51    inference(ennf_transformation,[],[f11])).
% 1.27/0.51  fof(f11,axiom,(
% 1.27/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 1.27/0.51  fof(f417,plain,(
% 1.27/0.51    ~spl5_6 | ~spl5_3 | spl5_46),
% 1.27/0.51    inference(avatar_split_clause,[],[f416,f413,f84,f96])).
% 1.27/0.51  fof(f416,plain,(
% 1.27/0.51    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | spl5_46),
% 1.27/0.51    inference(superposition,[],[f414,f55])).
% 1.27/0.51  fof(f55,plain,(
% 1.27/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f20])).
% 1.27/0.51  fof(f20,plain,(
% 1.27/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f5])).
% 1.27/0.51  fof(f5,axiom,(
% 1.27/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.27/0.51  fof(f414,plain,(
% 1.27/0.51    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | spl5_46),
% 1.27/0.51    inference(avatar_component_clause,[],[f413])).
% 1.27/0.51  fof(f415,plain,(
% 1.27/0.51    ~spl5_46 | ~spl5_14 | spl5_42),
% 1.27/0.51    inference(avatar_split_clause,[],[f411,f386,f180,f413])).
% 1.27/0.51  fof(f180,plain,(
% 1.27/0.51    spl5_14 <=> ! [X0] : (r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.27/0.51  fof(f386,plain,(
% 1.27/0.51    spl5_42 <=> r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.27/0.51  fof(f411,plain,(
% 1.27/0.51    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_14 | spl5_42)),
% 1.27/0.51    inference(resolution,[],[f403,f181])).
% 1.27/0.51  fof(f181,plain,(
% 1.27/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_14),
% 1.27/0.51    inference(avatar_component_clause,[],[f180])).
% 1.27/0.51  fof(f403,plain,(
% 1.27/0.51    ~r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1)) | spl5_42),
% 1.27/0.51    inference(avatar_component_clause,[],[f386])).
% 1.27/0.51  fof(f404,plain,(
% 1.27/0.51    ~spl5_42 | ~spl5_10 | spl5_45),
% 1.27/0.51    inference(avatar_split_clause,[],[f402,f399,f151,f386])).
% 1.27/0.51  fof(f151,plain,(
% 1.27/0.51    spl5_10 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.27/0.51  % (32000)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.27/0.51  fof(f402,plain,(
% 1.27/0.51    ~r2_hidden(k1_funct_1(k4_relat_1(sK1),sK0),k1_relat_1(sK1)) | (~spl5_10 | spl5_45)),
% 1.27/0.51    inference(resolution,[],[f400,f174])).
% 1.27/0.51  fof(f174,plain,(
% 1.27/0.51    ( ! [X2] : (r2_hidden(k1_funct_1(sK1,X2),k2_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl5_10),
% 1.27/0.51    inference(resolution,[],[f152,f73])).
% 1.27/0.51  fof(f73,plain,(
% 1.27/0.51    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 1.27/0.51    inference(equality_resolution,[],[f65])).
% 1.27/0.51  fof(f65,plain,(
% 1.27/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 1.27/0.51    inference(cnf_transformation,[],[f41])).
% 1.27/0.51  fof(f152,plain,(
% 1.27/0.51    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl5_10),
% 1.27/0.51    inference(avatar_component_clause,[],[f151])).
% 1.27/0.51  fof(f400,plain,(
% 1.27/0.51    ~r2_hidden(k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)),k2_relat_1(sK1)) | spl5_45),
% 1.27/0.51    inference(avatar_component_clause,[],[f399])).
% 1.27/0.51  fof(f311,plain,(
% 1.27/0.51    ~spl5_6 | ~spl5_3 | spl5_26),
% 1.27/0.51    inference(avatar_split_clause,[],[f309,f282,f84,f96])).
% 1.27/0.51  fof(f282,plain,(
% 1.27/0.51    spl5_26 <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.27/0.51  fof(f309,plain,(
% 1.27/0.51    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | spl5_26),
% 1.27/0.51    inference(resolution,[],[f307,f123])).
% 1.27/0.51  fof(f123,plain,(
% 1.27/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X1,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(resolution,[],[f74,f68])).
% 1.27/0.51  fof(f68,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f31])).
% 1.27/0.51  fof(f31,plain,(
% 1.27/0.51    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.27/0.51    inference(flattening,[],[f30])).
% 1.27/0.51  fof(f30,plain,(
% 1.27/0.51    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.27/0.51    inference(ennf_transformation,[],[f4])).
% 1.27/0.51  fof(f4,axiom,(
% 1.27/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.27/0.51  fof(f307,plain,(
% 1.27/0.51    ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | spl5_26),
% 1.27/0.51    inference(avatar_component_clause,[],[f282])).
% 1.27/0.51  fof(f308,plain,(
% 1.27/0.51    ~spl5_26 | ~spl5_10 | spl5_31),
% 1.27/0.51    inference(avatar_split_clause,[],[f306,f303,f151,f282])).
% 1.27/0.51  fof(f306,plain,(
% 1.27/0.51    ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_10 | spl5_31)),
% 1.27/0.51    inference(resolution,[],[f304,f174])).
% 1.27/0.51  fof(f304,plain,(
% 1.27/0.51    ~r2_hidden(k1_funct_1(sK1,sK4(sK1,sK0)),k2_relat_1(sK1)) | spl5_31),
% 1.27/0.51    inference(avatar_component_clause,[],[f303])).
% 1.27/0.51  fof(f273,plain,(
% 1.27/0.51    spl5_24 | ~spl5_3 | ~spl5_23),
% 1.27/0.51    inference(avatar_split_clause,[],[f268,f263,f84,f271])).
% 1.27/0.51  fof(f271,plain,(
% 1.27/0.51    spl5_24 <=> sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.27/0.51  fof(f263,plain,(
% 1.27/0.51    spl5_23 <=> ! [X2] : (sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2))) | ~r2_hidden(X2,k2_relat_1(sK1)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.27/0.51  fof(f268,plain,(
% 1.27/0.51    sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) | (~spl5_3 | ~spl5_23)),
% 1.27/0.51    inference(resolution,[],[f264,f85])).
% 1.27/0.51  fof(f264,plain,(
% 1.27/0.51    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2)))) ) | ~spl5_23),
% 1.27/0.51    inference(avatar_component_clause,[],[f263])).
% 1.27/0.51  fof(f265,plain,(
% 1.27/0.51    ~spl5_6 | spl5_23 | ~spl5_22),
% 1.27/0.51    inference(avatar_split_clause,[],[f260,f254,f263,f96])).
% 1.27/0.51  fof(f254,plain,(
% 1.27/0.51    spl5_22 <=> ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.27/0.51  fof(f260,plain,(
% 1.27/0.51    ( ! [X2] : (sK4(sK1,X2) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,X2))) | ~r2_hidden(X2,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl5_22),
% 1.27/0.51    inference(resolution,[],[f255,f123])).
% 1.27/0.51  fof(f255,plain,(
% 1.27/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl5_22),
% 1.27/0.51    inference(avatar_component_clause,[],[f254])).
% 1.27/0.51  fof(f256,plain,(
% 1.27/0.51    ~spl5_6 | ~spl5_5 | ~spl5_4 | spl5_22 | ~spl5_7),
% 1.27/0.51    inference(avatar_split_clause,[],[f250,f108,f254,f88,f92,f96])).
% 1.27/0.51  fof(f88,plain,(
% 1.27/0.51    spl5_4 <=> v2_funct_1(sK1)),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.27/0.51  fof(f250,plain,(
% 1.27/0.51    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl5_7),
% 1.27/0.51    inference(superposition,[],[f61,f109])).
% 1.27/0.51  fof(f61,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f27])).
% 1.27/0.51  fof(f27,plain,(
% 1.27/0.51    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.27/0.51    inference(flattening,[],[f26])).
% 1.27/0.51  fof(f26,plain,(
% 1.27/0.51    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.27/0.51    inference(ennf_transformation,[],[f12])).
% 1.27/0.51  fof(f12,axiom,(
% 1.27/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 1.27/0.51  fof(f225,plain,(
% 1.27/0.51    ~spl5_11 | ~spl5_6 | spl5_17 | ~spl5_15),
% 1.27/0.51    inference(avatar_split_clause,[],[f220,f212,f222,f96,f156])).
% 1.27/0.51  fof(f212,plain,(
% 1.27/0.51    spl5_15 <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.27/0.51  fof(f220,plain,(
% 1.27/0.51    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~spl5_15),
% 1.27/0.51    inference(superposition,[],[f57,f213])).
% 1.27/0.51  fof(f213,plain,(
% 1.27/0.51    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | ~spl5_15),
% 1.27/0.51    inference(avatar_component_clause,[],[f212])).
% 1.27/0.51  fof(f57,plain,(
% 1.27/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f21])).
% 1.27/0.51  fof(f21,plain,(
% 1.27/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f3])).
% 1.27/0.51  fof(f3,axiom,(
% 1.27/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.27/0.51  fof(f214,plain,(
% 1.27/0.51    ~spl5_6 | spl5_15 | ~spl5_6),
% 1.27/0.51    inference(avatar_split_clause,[],[f206,f96,f212,f96])).
% 1.27/0.51  fof(f206,plain,(
% 1.27/0.51    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl5_6),
% 1.27/0.51    inference(superposition,[],[f205,f102])).
% 1.27/0.51  fof(f102,plain,(
% 1.27/0.51    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(global_subsumption,[],[f53,f100])).
% 1.27/0.51  fof(f100,plain,(
% 1.27/0.51    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(superposition,[],[f54,f56])).
% 1.27/0.51  fof(f56,plain,(
% 1.27/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f20])).
% 1.27/0.51  fof(f54,plain,(
% 1.27/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f19])).
% 1.27/0.51  fof(f19,plain,(
% 1.27/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f7])).
% 1.27/0.51  fof(f7,axiom,(
% 1.27/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.27/0.51  fof(f53,plain,(
% 1.27/0.51    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f18])).
% 1.27/0.51  fof(f18,plain,(
% 1.27/0.51    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.27/0.51    inference(ennf_transformation,[],[f2])).
% 1.27/0.51  fof(f2,axiom,(
% 1.27/0.51    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.27/0.51  fof(f205,plain,(
% 1.27/0.51    ( ! [X6] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X6))) = k10_relat_1(k4_relat_1(sK1),X6)) ) | ~spl5_6),
% 1.27/0.51    inference(resolution,[],[f143,f97])).
% 1.27/0.51  fof(f97,plain,(
% 1.27/0.51    v1_relat_1(sK1) | ~spl5_6),
% 1.27/0.51    inference(avatar_component_clause,[],[f96])).
% 1.27/0.51  fof(f143,plain,(
% 1.27/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)) )),
% 1.27/0.51    inference(resolution,[],[f142,f53])).
% 1.27/0.51  fof(f142,plain,(
% 1.27/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)) )),
% 1.27/0.51    inference(resolution,[],[f134,f49])).
% 1.27/0.51  fof(f49,plain,(
% 1.27/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.27/0.51    inference(cnf_transformation,[],[f10])).
% 1.27/0.51  fof(f10,axiom,(
% 1.27/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.27/0.51  fof(f134,plain,(
% 1.27/0.51    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.27/0.51    inference(superposition,[],[f57,f51])).
% 1.27/0.51  fof(f51,plain,(
% 1.27/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.27/0.51    inference(cnf_transformation,[],[f6])).
% 1.27/0.51  fof(f6,axiom,(
% 1.27/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.27/0.51  fof(f182,plain,(
% 1.27/0.51    ~spl5_6 | spl5_14 | ~spl5_12),
% 1.27/0.51    inference(avatar_split_clause,[],[f178,f159,f180,f96])).
% 1.27/0.51  fof(f159,plain,(
% 1.27/0.51    spl5_12 <=> ! [X3] : (~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.27/0.51  fof(f178,plain,(
% 1.27/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(k4_relat_1(sK1),X0),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1)) ) | ~spl5_12),
% 1.27/0.51    inference(superposition,[],[f177,f56])).
% 1.27/0.51  fof(f177,plain,(
% 1.27/0.51    ( ! [X2] : (r2_hidden(k1_funct_1(k4_relat_1(sK1),X2),k2_relat_1(k4_relat_1(sK1))) | ~r2_hidden(X2,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_12),
% 1.27/0.51    inference(resolution,[],[f160,f73])).
% 1.27/0.51  fof(f160,plain,(
% 1.27/0.51    ( ! [X3] : (r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_12),
% 1.27/0.51    inference(avatar_component_clause,[],[f159])).
% 1.27/0.51  fof(f163,plain,(
% 1.27/0.51    ~spl5_6 | spl5_11),
% 1.27/0.51    inference(avatar_split_clause,[],[f162,f156,f96])).
% 1.27/0.51  fof(f162,plain,(
% 1.27/0.51    ~v1_relat_1(sK1) | spl5_11),
% 1.27/0.51    inference(resolution,[],[f157,f53])).
% 1.27/0.51  fof(f157,plain,(
% 1.27/0.51    ~v1_relat_1(k4_relat_1(sK1)) | spl5_11),
% 1.27/0.51    inference(avatar_component_clause,[],[f156])).
% 1.27/0.51  fof(f161,plain,(
% 1.27/0.51    ~spl5_11 | spl5_12 | ~spl5_9),
% 1.27/0.51    inference(avatar_split_clause,[],[f149,f120,f159,f156])).
% 1.27/0.51  fof(f149,plain,(
% 1.27/0.51    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1))) ) | ~spl5_9),
% 1.27/0.51    inference(resolution,[],[f75,f121])).
% 1.27/0.51  fof(f75,plain,(
% 1.27/0.51    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.27/0.51    inference(equality_resolution,[],[f72])).
% 1.27/0.51  fof(f72,plain,(
% 1.27/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f43])).
% 1.27/0.51  fof(f153,plain,(
% 1.27/0.51    ~spl5_6 | spl5_10 | ~spl5_5),
% 1.27/0.51    inference(avatar_split_clause,[],[f147,f92,f151,f96])).
% 1.27/0.51  fof(f147,plain,(
% 1.27/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) ) | ~spl5_5),
% 1.27/0.51    inference(resolution,[],[f75,f93])).
% 1.27/0.51  fof(f122,plain,(
% 1.27/0.51    ~spl5_6 | ~spl5_5 | spl5_9 | ~spl5_7),
% 1.27/0.51    inference(avatar_split_clause,[],[f113,f108,f120,f92,f96])).
% 1.27/0.51  fof(f113,plain,(
% 1.27/0.51    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_7),
% 1.27/0.51    inference(superposition,[],[f59,f109])).
% 1.27/0.51  fof(f59,plain,(
% 1.27/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f23])).
% 1.27/0.51  fof(f23,plain,(
% 1.27/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.51    inference(flattening,[],[f22])).
% 1.27/0.51  fof(f22,plain,(
% 1.27/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.51    inference(ennf_transformation,[],[f9])).
% 1.27/0.51  fof(f9,axiom,(
% 1.27/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.27/0.51  fof(f110,plain,(
% 1.27/0.51    ~spl5_6 | ~spl5_5 | spl5_7 | ~spl5_4),
% 1.27/0.51    inference(avatar_split_clause,[],[f103,f88,f108,f92,f96])).
% 1.27/0.51  fof(f103,plain,(
% 1.27/0.51    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_4),
% 1.27/0.51    inference(resolution,[],[f60,f89])).
% 1.27/0.51  fof(f89,plain,(
% 1.27/0.51    v2_funct_1(sK1) | ~spl5_4),
% 1.27/0.51    inference(avatar_component_clause,[],[f88])).
% 1.27/0.51  fof(f60,plain,(
% 1.27/0.51    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.27/0.51    inference(cnf_transformation,[],[f25])).
% 1.27/0.51  fof(f25,plain,(
% 1.27/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.51    inference(flattening,[],[f24])).
% 1.27/0.51  fof(f24,plain,(
% 1.27/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.51    inference(ennf_transformation,[],[f8])).
% 1.27/0.51  fof(f8,axiom,(
% 1.27/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.27/0.51  fof(f98,plain,(
% 1.27/0.51    spl5_6),
% 1.27/0.51    inference(avatar_split_clause,[],[f44,f96])).
% 1.27/0.51  fof(f44,plain,(
% 1.27/0.51    v1_relat_1(sK1)),
% 1.27/0.51    inference(cnf_transformation,[],[f35])).
% 1.27/0.51  fof(f35,plain,(
% 1.27/0.51    (sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.27/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f34])).
% 1.27/0.51  fof(f34,plain,(
% 1.27/0.51    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.27/0.51    introduced(choice_axiom,[])).
% 1.27/0.51  fof(f17,plain,(
% 1.27/0.51    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.27/0.51    inference(flattening,[],[f16])).
% 1.27/0.51  fof(f16,plain,(
% 1.27/0.51    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.27/0.51    inference(ennf_transformation,[],[f15])).
% 1.27/0.51  fof(f15,negated_conjecture,(
% 1.27/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.27/0.51    inference(negated_conjecture,[],[f14])).
% 1.27/0.51  fof(f14,conjecture,(
% 1.27/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 1.27/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 1.27/0.51  fof(f94,plain,(
% 1.27/0.51    spl5_5),
% 1.27/0.51    inference(avatar_split_clause,[],[f45,f92])).
% 1.27/0.51  fof(f45,plain,(
% 1.27/0.51    v1_funct_1(sK1)),
% 1.27/0.51    inference(cnf_transformation,[],[f35])).
% 1.27/0.51  fof(f90,plain,(
% 1.27/0.51    spl5_4),
% 1.27/0.51    inference(avatar_split_clause,[],[f46,f88])).
% 1.27/0.51  fof(f46,plain,(
% 1.27/0.51    v2_funct_1(sK1)),
% 1.27/0.51    inference(cnf_transformation,[],[f35])).
% 1.27/0.51  fof(f86,plain,(
% 1.27/0.51    spl5_3),
% 1.27/0.51    inference(avatar_split_clause,[],[f47,f84])).
% 1.27/0.51  fof(f47,plain,(
% 1.27/0.51    r2_hidden(sK0,k2_relat_1(sK1))),
% 1.27/0.51    inference(cnf_transformation,[],[f35])).
% 1.27/0.51  fof(f82,plain,(
% 1.27/0.51    ~spl5_1 | ~spl5_2),
% 1.27/0.51    inference(avatar_split_clause,[],[f48,f80,f77])).
% 1.27/0.51  fof(f77,plain,(
% 1.27/0.51    spl5_1 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 1.27/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.27/0.51  fof(f48,plain,(
% 1.27/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 1.27/0.51    inference(cnf_transformation,[],[f35])).
% 1.27/0.51  % SZS output end Proof for theBenchmark
% 1.27/0.51  % (31988)------------------------------
% 1.27/0.51  % (31988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.51  % (31988)Termination reason: Refutation
% 1.27/0.51  
% 1.27/0.51  % (31988)Memory used [KB]: 11513
% 1.27/0.51  % (31988)Time elapsed: 0.052 s
% 1.27/0.51  % (31988)------------------------------
% 1.27/0.51  % (31988)------------------------------
% 1.27/0.51  % (31976)Success in time 0.163 s
%------------------------------------------------------------------------------
