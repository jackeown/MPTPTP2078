%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 333 expanded)
%              Number of leaves         :   43 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  613 (1196 expanded)
%              Number of equality atoms :  113 ( 243 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f658,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f114,f125,f164,f172,f174,f278,f292,f299,f388,f397,f463,f487,f588,f602,f620,f630,f632,f634,f639,f657])).

fof(f657,plain,
    ( ~ spl5_70
    | ~ spl5_46
    | ~ spl5_65
    | ~ spl5_68
    | spl5_71 ),
    inference(avatar_split_clause,[],[f655,f637,f618,f600,f485,f628])).

fof(f628,plain,
    ( spl5_70
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f485,plain,
    ( spl5_46
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f600,plain,
    ( spl5_65
  <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f618,plain,
    ( spl5_68
  <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f637,plain,
    ( spl5_71
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f655,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_46
    | ~ spl5_65
    | ~ spl5_68
    | spl5_71 ),
    inference(trivial_inequality_removal,[],[f654])).

fof(f654,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_46
    | ~ spl5_65
    | ~ spl5_68
    | spl5_71 ),
    inference(forward_demodulation,[],[f653,f601])).

fof(f601,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f600])).

fof(f653,plain,
    ( sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_46
    | ~ spl5_68
    | spl5_71 ),
    inference(forward_demodulation,[],[f652,f619])).

fof(f619,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f618])).

fof(f652,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_46
    | spl5_71 ),
    inference(superposition,[],[f638,f486])).

fof(f486,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f485])).

fof(f638,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_71 ),
    inference(avatar_component_clause,[],[f637])).

fof(f639,plain,
    ( ~ spl5_71
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f635,f112,f82,f637])).

fof(f82,plain,
    ( spl5_2
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f112,plain,
    ( spl5_7
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f635,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f83,f113])).

fof(f113,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f83,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f634,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0)
    | k2_funct_1(sK1) != k4_relat_1(sK1)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f632,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_66 ),
    inference(avatar_split_clause,[],[f631,f611,f86,f98])).

fof(f98,plain,
    ( spl5_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f86,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f611,plain,
    ( spl5_66
  <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f631,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl5_66 ),
    inference(resolution,[],[f612,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f76,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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

fof(f612,plain,
    ( ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | spl5_66 ),
    inference(avatar_component_clause,[],[f611])).

fof(f630,plain,
    ( ~ spl5_66
    | spl5_70
    | ~ spl5_41
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f609,f600,f395,f628,f611])).

fof(f395,plain,
    ( spl5_41
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f609,plain,
    ( r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_41
    | ~ spl5_65 ),
    inference(superposition,[],[f396,f601])).

fof(f396,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1)))
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f395])).

fof(f620,plain,
    ( ~ spl5_66
    | spl5_68
    | ~ spl5_25
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f605,f600,f290,f618,f611])).

fof(f290,plain,
    ( spl5_25
  <=> ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f605,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)
    | ~ r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_25
    | ~ spl5_65 ),
    inference(superposition,[],[f291,f601])).

fof(f291,plain,
    ( ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f290])).

fof(f602,plain,
    ( spl5_65
    | ~ spl5_3
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f596,f586,f86,f600])).

fof(f586,plain,
    ( spl5_63
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f596,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_3
    | ~ spl5_63 ),
    inference(resolution,[],[f587,f87])).

fof(f87,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f587,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK4(sK1,X0)) = X0 )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f586])).

fof(f588,plain,
    ( ~ spl5_6
    | spl5_63
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f582,f94,f586,f98])).

fof(f94,plain,
    ( spl5_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f582,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK4(sK1,X0)) = X0
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f156,f95])).

fof(f95,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) = X1
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f73,f76])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f487,plain,
    ( ~ spl5_6
    | spl5_46
    | ~ spl5_5
    | ~ spl5_26
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f483,f461,f296,f94,f485,f98])).

fof(f296,plain,
    ( spl5_26
  <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f461,plain,
    ( spl5_43
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(sK1)
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) )
    | ~ spl5_5
    | ~ spl5_26
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f480,f297])).

fof(f297,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f296])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) )
    | ~ spl5_5
    | ~ spl5_43 ),
    inference(resolution,[],[f462,f95])).

fof(f462,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f461])).

fof(f463,plain,
    ( ~ spl5_12
    | spl5_43
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f454,f123,f461,f167])).

fof(f167,plain,
    ( spl5_12
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f123,plain,
    ( spl5_9
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f454,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6)))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6) )
    | ~ spl5_9 ),
    inference(resolution,[],[f65,f124])).

fof(f124,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(f397,plain,
    ( ~ spl5_12
    | spl5_41
    | ~ spl5_11
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f392,f386,f162,f395,f167])).

fof(f162,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f386,plain,
    ( spl5_40
  <=> ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f392,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl5_11
    | ~ spl5_40 ),
    inference(resolution,[],[f390,f70])).

fof(f390,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_11
    | ~ spl5_40 ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_11
    | ~ spl5_40 ),
    inference(resolution,[],[f387,f177])).

fof(f177,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(sK1,X2),k2_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f163,f75])).

fof(f75,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f163,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f386])).

fof(f388,plain,
    ( ~ spl5_6
    | spl5_40
    | ~ spl5_13
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f384,f290,f170,f386,f98])).

fof(f170,plain,
    ( spl5_13
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))
        | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))
        | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_13
    | ~ spl5_25 ),
    inference(superposition,[],[f358,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f358,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(k4_relat_1(sK1)))
        | r2_hidden(k4_tarski(k1_funct_1(sK1,X2),X2),k4_relat_1(sK1))
        | ~ r2_hidden(X2,k1_relat_1(sK1)) )
    | ~ spl5_13
    | ~ spl5_25 ),
    inference(superposition,[],[f171,f291])).

fof(f171,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f299,plain,
    ( ~ spl5_12
    | ~ spl5_6
    | spl5_26
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f294,f276,f296,f98,f167])).

fof(f276,plain,
    ( spl5_22
  <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f294,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl5_22 ),
    inference(superposition,[],[f59,f277])).

fof(f277,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f276])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f292,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_25
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f288,f112,f90,f290,f94,f98])).

fof(f90,plain,
    ( spl5_4
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f288,plain,
    ( ! [X0] :
        ( k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f287,f113])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f63,f91])).

fof(f91,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f278,plain,
    ( ~ spl5_6
    | spl5_22
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f269,f98,f276,f98])).

fof(f269,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(superposition,[],[f268,f107])).

fof(f107,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f54,f105])).

fof(f105,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f56,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f268,plain,
    ( ! [X6] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X6))) = k10_relat_1(k4_relat_1(sK1),X6)
    | ~ spl5_6 ),
    inference(resolution,[],[f186,f99])).

fof(f99,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1) ) ),
    inference(resolution,[],[f157,f54])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1) ) ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f59,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f174,plain,
    ( ~ spl5_6
    | spl5_12 ),
    inference(avatar_split_clause,[],[f173,f167,f98])).

fof(f173,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_12 ),
    inference(resolution,[],[f168,f54])).

fof(f168,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f172,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f160,f123,f170,f167])).

fof(f160,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))
        | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl5_9 ),
    inference(resolution,[],[f77,f124])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

% (23612)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (23614)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f164,plain,
    ( ~ spl5_6
    | spl5_11
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f158,f94,f162,f98])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f77,f95])).

fof(f125,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f116,f112,f123,f94,f98])).

% (23604)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f116,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f61,f113])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f114,plain,
    ( ~ spl5_6
    | ~ spl5_5
    | spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f108,f90,f112,f94,f98])).

fof(f108,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f62,f91])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f100,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f46,f98])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
      | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
    & r2_hidden(sK0,k2_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f36])).

fof(f36,plain,
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

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f96,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f48,f90])).

fof(f48,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f50,f82,f79])).

fof(f79,plain,
    ( spl5_1
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (23617)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (23609)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (23607)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (23619)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (23615)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (23616)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (23608)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (23603)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (23606)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (23611)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (23610)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (23601)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (23605)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (23607)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f658,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f114,f125,f164,f172,f174,f278,f292,f299,f388,f397,f463,f487,f588,f602,f620,f630,f632,f634,f639,f657])).
% 0.21/0.50  fof(f657,plain,(
% 0.21/0.50    ~spl5_70 | ~spl5_46 | ~spl5_65 | ~spl5_68 | spl5_71),
% 0.21/0.50    inference(avatar_split_clause,[],[f655,f637,f618,f600,f485,f628])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    spl5_70 <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 0.21/0.50  fof(f485,plain,(
% 0.21/0.50    spl5_46 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    spl5_65 <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.21/0.50  fof(f618,plain,(
% 0.21/0.50    spl5_68 <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.50  fof(f637,plain,(
% 0.21/0.50    spl5_71 <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_46 | ~spl5_65 | ~spl5_68 | spl5_71)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f654])).
% 0.21/0.50  fof(f654,plain,(
% 0.21/0.50    sK0 != sK0 | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_46 | ~spl5_65 | ~spl5_68 | spl5_71)),
% 0.21/0.50    inference(forward_demodulation,[],[f653,f601])).
% 0.21/0.50  fof(f601,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_65),
% 0.21/0.50    inference(avatar_component_clause,[],[f600])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_46 | ~spl5_68 | spl5_71)),
% 0.21/0.50    inference(forward_demodulation,[],[f652,f619])).
% 0.21/0.50  fof(f619,plain,(
% 0.21/0.50    k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) | ~spl5_68),
% 0.21/0.50    inference(avatar_component_clause,[],[f618])).
% 0.21/0.50  fof(f652,plain,(
% 0.21/0.50    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_46 | spl5_71)),
% 0.21/0.50    inference(superposition,[],[f638,f486])).
% 0.21/0.50  fof(f486,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0)) | ~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_46),
% 0.21/0.50    inference(avatar_component_clause,[],[f485])).
% 0.21/0.50  fof(f638,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | spl5_71),
% 0.21/0.50    inference(avatar_component_clause,[],[f637])).
% 0.21/0.50  fof(f639,plain,(
% 0.21/0.50    ~spl5_71 | spl5_2 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f635,f112,f82,f637])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl5_2 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl5_7 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | (spl5_2 | ~spl5_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f83,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f634,plain,(
% 0.21/0.50    k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0) | k2_funct_1(sK1) != k4_relat_1(sK1) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_3 | spl5_66),
% 0.21/0.50    inference(avatar_split_clause,[],[f631,f611,f86,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl5_6 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl5_3 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f611,plain,(
% 0.21/0.50    spl5_66 <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 0.21/0.50  fof(f631,plain,(
% 0.21/0.50    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | spl5_66),
% 0.21/0.50    inference(resolution,[],[f612,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X1,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(resolution,[],[f76,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.50    inference(rectify,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.50  fof(f612,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | spl5_66),
% 0.21/0.50    inference(avatar_component_clause,[],[f611])).
% 0.21/0.50  fof(f630,plain,(
% 0.21/0.50    ~spl5_66 | spl5_70 | ~spl5_41 | ~spl5_65),
% 0.21/0.50    inference(avatar_split_clause,[],[f609,f600,f395,f628,f611])).
% 0.21/0.50  fof(f395,plain,(
% 0.21/0.50    spl5_41 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.50  fof(f609,plain,(
% 0.21/0.50    r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_41 | ~spl5_65)),
% 0.21/0.50    inference(superposition,[],[f396,f601])).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1))) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl5_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f395])).
% 0.21/0.50  fof(f620,plain,(
% 0.21/0.50    ~spl5_66 | spl5_68 | ~spl5_25 | ~spl5_65),
% 0.21/0.50    inference(avatar_split_clause,[],[f605,f600,f290,f618,f611])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    spl5_25 <=> ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) | ~r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | (~spl5_25 | ~spl5_65)),
% 0.21/0.50    inference(superposition,[],[f291,f601])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f290])).
% 0.21/0.50  fof(f602,plain,(
% 0.21/0.50    spl5_65 | ~spl5_3 | ~spl5_63),
% 0.21/0.50    inference(avatar_split_clause,[],[f596,f586,f86,f600])).
% 0.21/0.50  fof(f586,plain,(
% 0.21/0.50    spl5_63 <=> ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.50  fof(f596,plain,(
% 0.21/0.50    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | (~spl5_3 | ~spl5_63)),
% 0.21/0.50    inference(resolution,[],[f587,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK4(sK1,X0)) = X0) ) | ~spl5_63),
% 0.21/0.50    inference(avatar_component_clause,[],[f586])).
% 0.21/0.50  fof(f588,plain,(
% 0.21/0.50    ~spl5_6 | spl5_63 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f582,f94,f586,f98])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_5 <=> v1_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1,X0)) = X0 | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f156,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    v1_funct_1(sK1) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0,X1)) = X1 | ~v1_relat_1(X0) | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f73,f76])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.50  fof(f487,plain,(
% 0.21/0.50    ~spl5_6 | spl5_46 | ~spl5_5 | ~spl5_26 | ~spl5_43),
% 0.21/0.50    inference(avatar_split_clause,[],[f483,f461,f296,f94,f485,f98])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl5_26 <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f461,plain,(
% 0.21/0.50    spl5_43 <=> ! [X5,X6] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.50  fof(f483,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(sK1) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) ) | (~spl5_5 | ~spl5_26 | ~spl5_43)),
% 0.21/0.50    inference(forward_demodulation,[],[f480,f297])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | ~spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f296])).
% 0.21/0.50  fof(f480,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X0) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X0))) ) | (~spl5_5 | ~spl5_43)),
% 0.21/0.50    inference(resolution,[],[f462,f95])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    ( ! [X6,X5] : (~v1_funct_1(X6) | ~v1_relat_1(X6) | ~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5))) ) | ~spl5_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f461])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    ~spl5_12 | spl5_43 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f454,f123,f461,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    spl5_12 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl5_9 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    ( ! [X6,X5] : (~r2_hidden(X5,k1_relat_1(k5_relat_1(k4_relat_1(sK1),X6))) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),X6),X5) = k1_funct_1(X6,k1_funct_1(k4_relat_1(sK1),X5)) | ~v1_relat_1(k4_relat_1(sK1)) | ~v1_funct_1(X6) | ~v1_relat_1(X6)) ) | ~spl5_9),
% 0.21/0.50    inference(resolution,[],[f65,f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v1_funct_1(k4_relat_1(sK1)) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    ~spl5_12 | spl5_41 | ~spl5_11 | ~spl5_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f392,f386,f162,f395,f167])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl5_11 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    spl5_40 <=> ! [X0] : (~r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK1,X1),k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1))) ) | (~spl5_11 | ~spl5_40)),
% 0.21/0.50    inference(resolution,[],[f390,f70])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl5_11 | ~spl5_40)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f389])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl5_11 | ~spl5_40)),
% 0.21/0.50    inference(resolution,[],[f387,f177])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ( ! [X2] : (r2_hidden(k1_funct_1(sK1,X2),k2_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1))) ) | ~spl5_11),
% 0.21/0.50    inference(resolution,[],[f163,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f162])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1))) ) | ~spl5_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f386])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    ~spl5_6 | spl5_40 | ~spl5_13 | ~spl5_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f384,f290,f170,f386,f98])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl5_13 <=> ! [X3] : (~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) | r2_hidden(k4_tarski(k1_funct_1(sK1,X0),X0),k4_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | (~spl5_13 | ~spl5_25)),
% 0.21/0.50    inference(superposition,[],[f358,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(k1_funct_1(sK1,X2),k1_relat_1(k4_relat_1(sK1))) | r2_hidden(k4_tarski(k1_funct_1(sK1,X2),X2),k4_relat_1(sK1)) | ~r2_hidden(X2,k1_relat_1(sK1))) ) | (~spl5_13 | ~spl5_25)),
% 0.21/0.50    inference(superposition,[],[f171,f291])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X3] : (r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) | ~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1)))) ) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f170])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~spl5_12 | ~spl5_6 | spl5_26 | ~spl5_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f294,f276,f296,f98,f167])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl5_22 <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_relat_1(sK1)) | ~spl5_22),
% 0.21/0.50    inference(superposition,[],[f59,f277])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | ~spl5_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_5 | spl5_25 | ~spl5_4 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f288,f112,f90,f290,f94,f98])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl5_4 <=> v2_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl5_4 | ~spl5_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f287,f113])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f63,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    v2_funct_1(sK1) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~spl5_6 | spl5_22 | ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f269,f98,f276,f98])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl5_6),
% 0.21/0.50    inference(superposition,[],[f268,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(global_subsumption,[],[f54,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_relat_1(k1_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(superposition,[],[f56,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    ( ! [X6] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X6))) = k10_relat_1(k4_relat_1(sK1),X6)) ) | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f186,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v1_relat_1(sK1) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k4_relat_1(X0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f157,f54])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f128,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(superposition,[],[f59,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~spl5_6 | spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f173,f167,f98])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl5_12),
% 0.21/0.50    inference(resolution,[],[f168,f54])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~v1_relat_1(k4_relat_1(sK1)) | spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f167])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl5_12 | spl5_13 | ~spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f123,f170,f167])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(k4_relat_1(sK1))) | r2_hidden(k4_tarski(X3,k1_funct_1(k4_relat_1(sK1),X3)),k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1))) ) | ~spl5_9),
% 0.21/0.50    inference(resolution,[],[f77,f124])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  % (23612)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (23614)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~spl5_6 | spl5_11 | ~spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f94,f162,f98])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1) | ~v1_relat_1(sK1)) ) | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f77,f95])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_5 | spl5_9 | ~spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f116,f112,f123,f94,f98])).
% 0.21/0.50  % (23604)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_7),
% 0.21/0.50    inference(superposition,[],[f61,f113])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~spl5_6 | ~spl5_5 | spl5_7 | ~spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f90,f112,f94,f98])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    k2_funct_1(sK1) = k4_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f62,f91])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f98])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    (sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))) & r2_hidden(sK0,k2_relat_1(sK1)) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f94])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f90])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v2_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f86])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f82,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl5_1 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23607)------------------------------
% 0.21/0.51  % (23607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23607)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23607)Memory used [KB]: 11257
% 0.21/0.51  % (23607)Time elapsed: 0.095 s
% 0.21/0.51  % (23607)------------------------------
% 0.21/0.51  % (23607)------------------------------
% 0.21/0.51  % (23600)Success in time 0.15 s
%------------------------------------------------------------------------------
